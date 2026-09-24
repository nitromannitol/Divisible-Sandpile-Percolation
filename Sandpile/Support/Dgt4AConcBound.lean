/-
**The conditional concentration bound for `\Theta_n`** (`sandpile.tex:5267-5271`).

This is the assembly of the four ingredients: the Gaussian concentration inequality for a
functional Lipschitz for the `\ell^2` distance, cited at `sandpile.tex:5267` and frozen as
`External.GaussianLipschitzConcentration`; the rank-one reduction as a contraction, which is
what makes the bound survive the conditioning; the Lipschitz constant
`|c|\,\|\sum_{j\geq k_n+1}p_j(0,\cdot)\|` of `\Theta_n`, which is the square root of the
paper's "Gaussian concentration proxy"; and the measurability of `\Theta_n` in the residual.

One guard is needed.  `\Theta_n` is built from the box limit of
`eq:dgt4-infinite-green-field`, which takes its junk value where the limit does not exist,
and the Lipschitz hypothesis of the inequality is a statement at every configuration.  The
residuals at which the limit exists are a measurable set invariant under moves of finite
`\ell^2` length, so cutting `\Theta_n` off outside it changes nothing almost everywhere and
makes the Lipschitz bound hold everywhere.
-/
import Sandpile.Support.Dgt4AConcMeas
import Sandpile.Support.Dgt4AConcResid

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The residuals whose conditioned scenery has a Green field at every site. -/
def condConv (d : ℕ) (hd : 5 ≤ d) (c s : ℝ) : Set (Site d → ℝ) :=
  {r | ∀ y : Site d, condScenery d hd c r s ∈ greenConvAt d y}

theorem measurableSet_condConv (hd : 5 ≤ d) (c s : ℝ) :
    MeasurableSet (condConv d hd c s) := by
  have hrw : condConv d hd c s
      = ⋂ y : Site d, (fun r : Site d → ℝ => condScenery d hd c r s) ⁻¹' greenConvAt d y := by
    ext r
    simp [condConv, Set.mem_iInter]
  rw [hrw]
  exact MeasurableSet.iInter fun y =>
    (measurable_condScenery hd c s) (measurableSet_greenConvAt y)

/-- The guard is invariant under a move of finite `\ell^2` length. -/
theorem mem_condConv_of_hasSum (hd : 5 ≤ d) (c s : ℝ) {r r' : Site d → ℝ} {M : ℝ}
    (hM : HasSum (fun z => (r z - r' z) ^ 2) M) (hr : r ∈ condConv d hd c s) :
    r' ∈ condConv d hd c s :=
  (exists_tendsto_infiniteGreenField_sub hd (condScenery d hd c r s)
    (condScenery d hd c r' s) (c ^ 2 * M) (hasSum_sq_condScenery_sub hd c s r r' M hM) hr).1

/-- `\Theta_n` with its junk branch cut off. -/
noncomputable def condThetaG (d : ℕ) (hd : 5 ≤ d) (c s a : ℝ) (t j : ℕ) :
    (Site d → ℝ) → ℝ :=
  (condConv d hd c s).indicator (condTheta d hd c s a t j)

theorem measurable_condThetaG (hd : 5 ≤ d) (c s a : ℝ) (t j : ℕ) :
    Measurable (condThetaG d hd c s a t j) :=
  (measurable_condTheta hd c s a t j).indicator (measurableSet_condConv hd c s)

/-- Almost every residual is in the guard. -/
theorem ae_mem_condConv (hd : 5 ≤ d) (c s : ℝ) :
    ∀ᵐ r ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)), r ∈ condConv d hd c s := by
  have hres : ∀ᵐ r ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)), ∀ y : Site d,
      ∃ L : ℝ, Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z)
        atTop (𝓝 L) := by
    rw [ae_all_iff]
    exact fun y => ae_exists_tendsto_greenPartialSum_resid hd y
  filter_upwards [hres] with r hr
  exact fun y => exists_tendsto_infiniteGreenFieldPartial_shift hd c hr s y

theorem ae_condThetaG_eq (hd : 5 ≤ d) (c s a : ℝ) (t j : ℕ) :
    condThetaG d hd c s a t j
      =ᵐ[(LatticeProb.gaussLaw (Site d)).map (residField d hd)] condTheta d hd c s a t j := by
  filter_upwards [ae_mem_condConv hd c s] with r hr
  rw [condThetaG, Set.indicator_of_mem hr]

/-- **The guarded `\Theta_n` is Lipschitz at every pair of residuals.** -/
theorem abs_condThetaG_sub_le (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (c s a : ℝ) (t j : ℕ) (hj : 1 ≤ j) (Λ : ℝ)
    (hΛ : |c| * ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ ≤ Λ)
    (r r' : Site d → ℝ) (M : ℝ) (hM : HasSum (fun z => (r z - r' z) ^ 2) M) :
    |condThetaG d hd c s a t j r - condThetaG d hd c s a t j r'| ≤ Λ * Real.sqrt M := by
  have hMnn : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  by_cases hr : r ∈ condConv d hd c s
  · have hr' : r' ∈ condConv d hd c s := mem_condConv_of_hasSum hd c s hM hr
    rw [condThetaG, Set.indicator_of_mem hr, Set.indicator_of_mem hr']
    refine (abs_condTheta_sub_le hGH hd c s a t j hj r r' M hM (fun y => hr y)).trans ?_
    exact mul_le_mul_of_nonneg_right hΛ hMnn
  · have hr' : r' ∉ condConv d hd c s := by
      intro hmem
      have hM' : HasSum (fun z => (r' z - r z) ^ 2) M := by
        refine hM.congr_fun fun z => ?_
        ring
      exact hr (mem_condConv_of_hasSum hd c s hM' hmem)
    rw [condThetaG, Set.indicator_of_notMem hr, Set.indicator_of_notMem hr']
    have hΛnn : 0 ≤ Λ := le_trans (by positivity) hΛ
    simpa using mul_nonneg hΛnn hMnn

/-- **The conditional concentration tail of `\Theta_n`** (`sandpile.tex:5262-5266`): at a
fixed conditioning level, `\Theta_n` exceeds its conditional mean by `τ` with probability at
most `exp(-τ²/(2Λ²))`, for any `Λ` at least the paper's concentration proxy
`|c|\,\|\sum_{j\geq k_n+1}p_j(0,\cdot)\|`. -/
theorem measure_resid_condTheta_ge_le
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (c s a : ℝ) (t j : ℕ) (hj : 1 ≤ j) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : |c| * ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ ≤ Λ)
    (hint : Integrable (condTheta d hd c s a t j)
      ((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        {r | (∫ r', condTheta d hd c s a t j r'
              ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd))) + τ
            ≤ condTheta d hd c s a t j r}
      ≤ ENNReal.ofReal (Real.exp (-(τ ^ 2) / (2 * Λ ^ 2))) := by
  set ρ : Measure (Site d → ℝ) := (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  have hae := ae_condThetaG_eq hd c s a t j
  have hintG : Integrable (condThetaG d hd c s a t j) ρ := hint.congr hae.symm
  have hmean : ∫ r, condThetaG d hd c s a t j r ∂ρ = ∫ r, condTheta d hd c s a t j r ∂ρ :=
    integral_congr_ae hae
  have hconc := measure_resid_ge_integral_le hGaussConc hd (condThetaG d hd c s a t j) Λ hΛpos
    (measurable_condThetaG hd c s a t j) hintG
    (fun r r' M hM => abs_condThetaG_sub_le hGH hd c s a t j hj Λ hΛ r r' M hM) τ hτ
  rw [hmean] at hconc
  refine le_trans (le_of_eq ?_) hconc
  refine measure_congr ?_
  filter_upwards [hae] with r hr
  exact congrArg
    (fun u : ℝ => (∫ r', condTheta d hd c s a t j r' ∂ρ) + τ ≤ u) hr.symm

/-- The pointwise bound of `\Theta_n` by the terminal quantity of Step 2. -/
theorem abs_condTheta_le_condTerminal (hd : 5 ≤ d) (c s a : ℝ) (t j : ℕ) (r : Site d → ℝ) :
    |condTheta d hd c s a t j r| ≤ condTerminal d hd c s a t j r := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have h := abs_avgIterate_sub_le
    (fun y => infiniteGreenField (condScenery d hd c r s) y
      - odometerOf (condScenery d hd c r s) t y + a)
    (fun _ : Site d => (0 : ℝ)) j 0
  rw [avg_iterate_const hd1 j (0 : ℝ) 0] at h
  simpa [condTheta, condTerminal] using h

/-- **The conditional expectation of `\Theta_n` exists at every level.** -/
theorem integrable_condTheta (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) (a : ℝ) (t k : ℕ)
    (hk : 1 ≤ k) (s : ℝ) :
    Integrable (condTheta d hd (Real.sqrt (v : ℝ)) s a t k)
      ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) := by
  refine Integrable.mono' (integrable_condTerminal hGH hd v hsq a t k hk s)
    (measurable_condTheta hd (Real.sqrt (v : ℝ)) s a t k).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun r => ?_
  rw [Real.norm_eq_abs]
  exact abs_condTheta_le_condTerminal hd _ s a t k r

/-- **The conditional concentration tail of `\Theta_n` at a Gaussian scenery**
(`sandpile.tex:5262-5277`), with every hypothesis discharged except the cited inequality
itself. -/
theorem measure_resid_condTheta_ge_le_gauss
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v))
    (s a : ℝ) (t j : ℕ) (hj : 1 ≤ j) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : Real.sqrt (v : ℝ) * ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ ≤ Λ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        {r | (∫ r', condTheta d hd (Real.sqrt (v : ℝ)) s a t j r'
              ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd))) + τ
            ≤ condTheta d hd (Real.sqrt (v : ℝ)) s a t j r}
      ≤ ENNReal.ofReal (Real.exp (-(τ ^ 2) / (2 * Λ ^ 2))) := by
  refine measure_resid_condTheta_ge_le hGaussConc hGH hd (Real.sqrt (v : ℝ)) s a t j hj Λ hΛpos
    ?_ (integrable_condTheta hGH hd v hsq a t j hj s) τ hτ
  rwa [abs_of_nonneg (Real.sqrt_nonneg _)]

end Sandpile
