import Sandpile.Support.Dgt4ACondIntegrable
import Sandpile.Support.Dgt4ACovIterate
import Sandpile.Support.Dgt4ACondMeas
import Sandpile.Support.Dgt4AStep2Prep
import Sandpile.Support.Dgt4AStep2Site
import Sandpile.Support.Stationary

/-!
# The terminal quantity of Step 2 at every level

**The terminal quantity of Step 2 at the conditioned level** (`sandpile.tex:5092-5131`):
the object `P^{k+1}|V_\infty-u_t+a|(0)` read as a function of the residual, its
measurability, and the integrability of the conditional expectation at EVERY level.

The conditional expectation exists for almost every level by
`ae_integrable_gaussLaw_shift`; the Lipschitz bound of `Support/Dgt4ACovIterate.lean` in
the level then carries integrability from one level to all of them, which is what the
comparison of Step 2 needs at the particular level `\E u_n(0)+\Sigma^2y/\E u_n(0)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The conditioned scenery depends measurably on the residual. -/
theorem measurable_condScenery (hd : 5 ≤ d) (c s : ℝ) :
    Measurable (fun r : Site d → ℝ => condScenery d hd c r s) := by
  refine measurable_pi_iff.2 fun z => ?_
  have h1 : Measurable fun r : Site d → ℝ => r z + s * (greenUnit d hd : Site d → ℝ) z :=
    (measurable_pi_apply z).add measurable_const
  exact h1.const_mul c

/-- The terminal quantity of Step 2, as a function of the residual. -/
noncomputable def condTerminal (d : ℕ) (hd : 5 ≤ d) (c s a : ℝ) (t k : ℕ)
    (r : Site d → ℝ) : ℝ :=
  (avg^[k] (fun y => |infiniteGreenField (condScenery d hd c r s) y
    - odometerOf (condScenery d hd c r s) t y + a|)) 0

/-- The terminal quantity is almost everywhere measurable in the residual. -/
theorem aemeasurable_condTerminal (hd : 5 ≤ d) (c s a : ℝ) (t k : ℕ) :
    AEMeasurable (condTerminal d hd c s a t k)
      ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) := by
  have he : condTerminal d hd c s a t k
      = fun r : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) k, heatKernel d k 0 z *
        |infiniteGreenField (condScenery d hd c r s) z
          - odometerOf (condScenery d hd c r s) t z + a| := by
    funext r
    exact avg_iterate_eq_finsetSum _ _ _
  rw [he]
  have hterm : ∀ z : Site d, AEMeasurable (fun r : Site d → ℝ =>
      heatKernel d k 0 z * |infiniteGreenField (condScenery d hd c r s) z
        - odometerOf (condScenery d hd c r s) t z + a|)
      ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) := by
    intro z
    refine AEMeasurable.const_mul ?_ _
    refine AEMeasurable.abs ?_
    refine AEMeasurable.add ?_ aemeasurable_const
    exact (aemeasurable_infiniteGreenField_condScenery hd c s z).sub
      ((measurable_odometerOf t z).comp (measurable_condScenery hd c s)).aemeasurable
  have h := Finset.aemeasurable_sum
    (μ := (LatticeProb.gaussLaw (Site d)).map (residField d hd))
    (boxFinset (0 : Site d) k)
    (f := fun (z : Site d) (r : Site d → ℝ) => heatKernel d k 0 z *
      |infiniteGreenField (condScenery d hd c r s) z
        - odometerOf (condScenery d hd c r s) t z + a|)
    (fun z _ => hterm z)
  have heq : (∑ i ∈ boxFinset (0 : Site d) k,
        fun r : Site d → ℝ => heatKernel d k 0 i *
          |infiniteGreenField (condScenery d hd c r s) i
            - odometerOf (condScenery d hd c r s) t i + a|)
      = fun r : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) k, heatKernel d k 0 z *
        |infiniteGreenField (condScenery d hd c r s) z
          - odometerOf (condScenery d hd c r s) t z + a| := by
    funext r
    simp [Finset.sum_apply]
  rwa [heq] at h

/-- **The conditional expectation of the terminal quantity exists at EVERY level.**  It
exists at almost every level because the whole object is integrable on the product of the
level and the residual; the Lipschitz bound in the level then carries it to every level. -/
theorem integrable_condTerminal (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) (a : ℝ) (t k : ℕ)
    (hk : 1 ≤ k) (s : ℝ) :
    Integrable (condTerminal d hd (Real.sqrt (v : ℝ)) s a t k)
      ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) := by
  obtain ⟨C, hC, hlip⟩ := exists_avgIterate_abs_condScenery_deviation_le hGH hd
  set ρ : Measure (Site d → ℝ) := (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  set cc : ℝ := Real.sqrt (v : ℝ) with hcc
  set L : ℝ := C * ‖greenLp d hd (0 : Site d)‖ * (k : ℝ) ^ ((4 - (d : ℝ)) / 4) with hL
  have hGint : Integrable (fun ζ : Site d → ℝ =>
      (avg^[k] (fun x => |infiniteGreenField ζ x - odometerOf ζ t x + a|)) 0)
      (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
    (memLp_two_avgIterate (gaussianReal 0 v)
      (fun ζ y => |infiniteGreenField ζ y - odometerOf ζ t y + a|)
      (fun y => (memLp_two_centeredValue_site hd v hsq t a y).abs) k).integrable (by norm_num)
  have hae := ae_integrable_iidLaw_gauss_shift hd v _ hGint
  obtain ⟨s₀, hs₀⟩ := hae.exists
  have hres : ∀ᵐ r ∂ρ, ∀ y : Site d, ∃ M : ℝ,
      Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 M) := by
    rw [ae_all_iff]
    exact fun y => ae_exists_tendsto_greenPartialSum_resid hd y
  have hbound : ∀ᵐ r ∂ρ, |condTerminal d hd cc s a t k r|
      ≤ |condTerminal d hd cc s₀ a t k r| + L * |cc * (s - s₀)| := by
    filter_upwards [hres] with r hr
    have h := hlip cc r hr s₀ (s - s₀) a t k hk
    rw [show s₀ + (s - s₀) = s by ring] at h
    have h2 : |condTerminal d hd cc s a t k r - condTerminal d hd cc s₀ a t k r|
        ≤ L * |cc * (s - s₀)| := h
    have h3 := abs_sub_abs_le_abs_sub (condTerminal d hd cc s a t k r)
      (condTerminal d hd cc s₀ a t k r)
    linarith
  have hmaj : Integrable (fun r : Site d → ℝ =>
      |condTerminal d hd cc s₀ a t k r| + L * |cc * (s - s₀)|) ρ := by
    refine Integrable.add ?_ (integrable_const _)
    exact (hs₀.congr (Filter.Eventually.of_forall fun r => rfl)).abs
  refine Integrable.mono' hmaj (aemeasurable_condTerminal hd cc s a t k).aestronglyMeasurable ?_
  filter_upwards [hbound] with r hr
  simpa [Real.norm_eq_abs] using hr

end Sandpile
