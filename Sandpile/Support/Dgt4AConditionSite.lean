/-
The conditioning of `Support/Dgt4ACondition.lean` at a GENERAL site, which is the
linear regression formula of Step 3 (`sandpile.tex:5165-5175`).

At the conditioned level `s` the field at a site `x` splits as

  `V_\infty(x)=\sqrt v\,L_x(r)+\sqrt v\,s\,\|G(0,\cdot)\|^{-1}\sum_zG(x,z)G(0,z)`,

a residual random variable plus a deterministic term.  Since the conditioned value is
`V_\infty(0)=\sqrt v\,s\,\|G(0,\cdot)\|`, the deterministic term is
`V_\infty(0)\Cov(V_\infty(x),V_\infty(0))/\Sigma^2`, which is exactly the paper's
"conditional mean of the mean-zero Gaussian field is its linear regression on the
conditioned value".  At `x=0` the residual limit is `0` and this is
`Support/Dgt4AConditionField.lean`.

The residual limit exists almost surely; the statement is the one that transports
along the law of the residual field, because the existence of a limit of measurable
functions is a measurable condition even when the limit depends on the point.
-/
import Sandpile.Support.Dgt4ACovSuper
import Sandpile.Support.Dgt4AConditionField

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The Green partial sums at a general site of the conditioned direction converge to the
Green covariance divided by `\|G(0,\cdot)\|`. -/
theorem tendsto_greenPartialSum_greenUnit_site (hd : 5 ≤ d) (x : Site d) :
    Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n,
        green d x z * (greenUnit d hd : Site d → ℝ) z) atTop
      (𝓝 (‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' z : Site d, green d x z * green d 0 z)) := by
  have hsum := (tendsto_sum_boxFinset (summable_green_mul hd x 0)).const_mul
    ‖greenLp d hd (0 : Site d)‖⁻¹
  refine hsum.congr fun n => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by rw [coeFn_greenUnit hd z]; ring

theorem infiniteGreenFieldPartial_boxFinset_site (n : ℕ) (ζ : Site d → ℝ) (x : Site d) :
    infiniteGreenFieldPartial n ζ x = ∑ z ∈ boxFinset (0 : Site d) n, green d x z * ζ z := by
  rw [infiniteGreenFieldPartial,
    Finset.sum_set_coe (f := fun z : Site d => green d x z * ζ z) (greenFieldBox d n),
    greenFieldBox_toFinset]

/-- **The linear regression formula of Step 3** (`sandpile.tex:5160-5170`): at the
conditioned level the field at a site is a residual random variable plus
`V_\infty(0)\Cov(V_\infty(x),V_\infty(0))/\Sigma^2`. -/
theorem infiniteGreenField_shift_eq_site (hd : 5 ≤ d) (c : ℝ) (x : Site d) {r : Site d → ℝ}
    {L : ℝ}
    (hr : Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n, green d x z * r z) atTop (𝓝 L))
    (s : ℝ) :
    infiniteGreenField (fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z)) x
      = c * L + c * s * (‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' z : Site d, green d x z * green d 0 z)
      := by
  have hsum : ∀ n : ℕ,
      infiniteGreenFieldPartial n
          (fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z)) x
        = c * (∑ z ∈ boxFinset (0 : Site d) n, green d x z * r z)
          + c * s * ∑ z ∈ boxFinset (0 : Site d) n,
            green d x z * (greenUnit d hd : Site d → ℝ) z := by
    intro n
    rw [infiniteGreenFieldPartial_boxFinset_site, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  have htend : Tendsto (fun n : ℕ => infiniteGreenFieldPartial n
        (fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z)) x) atTop
      (𝓝 (c * L + c * s *
        (‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' z : Site d, green d x z * green d 0 z))) := by
    simp only [hsum]
    exact (hr.const_mul c).add
      ((tendsto_greenPartialSum_greenUnit_site hd x).const_mul (c * s))
  have hex : ∃ M : ℝ, Tendsto (fun n : ℕ => infiniteGreenFieldPartial n
      (fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z)) x) atTop (𝓝 M) := ⟨_, htend⟩
  rw [infiniteGreenField, dif_pos hex]
  exact tendsto_nhds_unique (Classical.choose_spec hex) htend

/-- The residual limit at a general site exists almost surely. -/
theorem ae_exists_tendsto_greenPartialSum_resid (hd : 5 ≤ d) (x : Site d) :
    ∀ᵐ r ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)),
      ∃ L : ℝ, Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n, green d x z * r z)
        atTop (𝓝 L) := by
  have hm : MeasurableSet {r : Site d → ℝ | ∃ L : ℝ,
      Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n, green d x z * r z) atTop (𝓝 L)} := by
    refine measurableSet_exists_tendsto fun n => ?_
    exact Finset.measurable_sum _ fun z _ => (measurable_pi_apply z).const_mul _
  rw [ae_map_iff (measurable_residField hd).aemeasurable hm]
  filter_upwards [ae_tendsto_greenPartialSum hd x] with ω hω
  refine ⟨⇑(LatticeProb.gaussIso (greenLp d hd x)) ω
    - condCoord d hd ω * (‖greenLp d hd (0 : Site d)‖⁻¹
      * ∑' z : Site d, green d x z * green d 0 z), ?_⟩
  have hlim := hω.sub ((tendsto_greenPartialSum_greenUnit_site hd x).const_mul
    (condCoord d hd ω))
  refine hlim.congr fun n => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun z _ => by simp only [residField]; ring

end Sandpile
