/-
What the conditioning of `Support/Dgt4ACondition.lean` does to the Green field
itself: at the conditioned level `s` the value `V_\infty(0)` is DETERMINISTIC and
equal to `\sqrt v\,\|G(0,\cdot)\|\,s`, which is the paper's `-V_\infty(0)=b` at
`sandpile.tex:5109`.

The residual field carries no Green mass at the origin: the box sums
`\sum_{|z|\leq n}G(0,z)\rho(\omega)(z)` tend to `0` almost surely, because they are
the Green partial sums of `\omega` minus `\xi(\omega)` times the deterministic
partial sums of `e`, and both tend to `\|G(0,\cdot)\|\xi(\omega)`.  Adding `se`
back therefore produces exactly `\sqrt v\,s\,\|G(0,\cdot)\|`.

The deterministic limit `\sum_{|z|\leq n}G(0,z)e(z)\to\|G(0,\cdot)\|` is the box
exhaustion of the summable family `G(0,\cdot)^2` divided by the norm.
-/
import Sandpile.Support.Dgt4ACondition

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

theorem coeFn_greenUnit (hd : 5 ≤ d) (z : Site d) :
    (greenUnit d hd : Site d → ℝ) z = ‖greenLp d hd (0 : Site d)‖⁻¹ * green d 0 z := by
  rw [greenUnit]
  simp [coeFn_greenLp]

theorem tendsto_boxFinset_atTop (x : Site d) :
    Tendsto (fun n : ℕ => boxFinset x n) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) (fun z => ⟨boxDist x z, ?_⟩)
  · intro z hz
    rw [mem_boxFinset_iff] at hz ⊢
    omega
  · rw [mem_boxFinset_iff]

theorem tendsto_sum_boxFinset {f : Site d → ℝ} (hf : Summable f) :
    Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n, f z) atTop (𝓝 (∑' z, f z)) :=
  hf.hasSum.comp (tendsto_boxFinset_atTop 0)

/-- The Green partial sums of the conditioned direction converge to `\|G(0,\cdot)\|`. -/
theorem tendsto_greenPartialSum_greenUnit (hd : 5 ≤ d) :
    Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n,
        green d 0 z * (greenUnit d hd : Site d → ℝ) z) atTop
      (𝓝 ‖greenLp d hd (0 : Site d)‖) := by
  have hpos := norm_greenLp_pos hd
  have hsum := (tendsto_sum_boxFinset (summable_green_sq hd (0 : Site d))).const_mul
    ‖greenLp d hd (0 : Site d)‖⁻¹
  have hval : ‖greenLp d hd (0 : Site d)‖⁻¹ * (∑' z : Site d, green d 0 z ^ 2)
      = ‖greenLp d hd (0 : Site d)‖ := by
    rw [← greenSqSum, ← norm_greenLp_sq hd]
    field_simp
  rw [hval] at hsum
  refine hsum.congr fun n => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by rw [coeFn_greenUnit hd z]; ring

theorem ae_coeFn_gaussIso_greenLp (hd : 5 ≤ d) :
    ⇑(LatticeProb.gaussIso (greenLp d hd (0 : Site d))) =ᵐ[LatticeProb.gaussLaw (Site d)]
      fun ω => ‖greenLp d hd (0 : Site d)‖ * condCoord d hd ω := by
  have hsm : LatticeProb.gaussIso (greenLp d hd (0 : Site d))
      = ‖greenLp d hd (0 : Site d)‖ • LatticeProb.gaussIso (greenUnit d hd) := by
    rw [← map_smul]
    congr 1
    rw [greenUnit, smul_smul, mul_inv_cancel₀ (norm_greenLp_pos hd).ne', one_smul]
  rw [hsm]
  filter_upwards [Lp.coeFn_smul ‖greenLp d hd (0 : Site d)‖
    (LatticeProb.gaussIso (greenUnit d hd))] with ω hω
  rw [hω]
  simp [condCoord]

theorem ae_tendsto_greenPartialSum_residField (hd : 5 ≤ d) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n, green d 0 z * residField d hd ω z)
        atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_greenPartialSum hd (0 : Site d), ae_coeFn_gaussIso_greenLp hd]
    with ω h1 h2
  have hlim := h1.sub ((tendsto_greenPartialSum_greenUnit hd).const_mul (condCoord d hd ω))
  rw [h2] at hlim
  have hz : ‖greenLp d hd (0 : Site d)‖ * condCoord d hd ω
      - condCoord d hd ω * ‖greenLp d hd (0 : Site d)‖ = 0 := by ring
  rw [hz] at hlim
  refine hlim.congr fun n => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun z _ => by simp only [residField]; ring

/-- **The residual field carries no Green mass at the origin.** -/
theorem ae_tendsto_greenPartialSum_resid (hd : 5 ≤ d) :
    ∀ᵐ r ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)),
      Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n, green d 0 z * r z) atTop (𝓝 0) := by
  have hm : MeasurableSet {r : Site d → ℝ |
      Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n, green d 0 z * r z) atTop
        (𝓝 (0 : ℝ))} := by
    refine measurableSet_tendsto (𝓝 (0 : ℝ)) fun n => ?_
    exact Finset.measurable_sum _ fun z _ => (measurable_pi_apply z).const_mul _
  rw [ae_map_iff (measurable_residField hd).aemeasurable hm]
  exact ae_tendsto_greenPartialSum_residField hd

theorem infiniteGreenFieldPartial_boxFinset (n : ℕ) (ζ : Site d → ℝ) :
    infiniteGreenFieldPartial n ζ (0 : Site d)
      = ∑ z ∈ boxFinset (0 : Site d) n, green d 0 z * ζ z := by
  rw [infiniteGreenFieldPartial,
    Finset.sum_set_coe (f := fun z : Site d => green d 0 z * ζ z) (greenFieldBox d n),
    greenFieldBox_toFinset]

/-- **At the conditioned level the Green field at the origin is deterministic**
(`sandpile.tex:5104`): `V_\infty(0)=\sqrt v\,s\,\|G(0,\cdot)\|`. -/
theorem infiniteGreenField_shift_eq (hd : 5 ≤ d) (c : ℝ) {r : Site d → ℝ}
    (hr : Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n, green d 0 z * r z) atTop (𝓝 0))
    (s : ℝ) :
    infiniteGreenField (fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z)) (0 : Site d)
      = c * s * ‖greenLp d hd (0 : Site d)‖ := by
  have hsum : ∀ n : ℕ,
      infiniteGreenFieldPartial n
          (fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z)) (0 : Site d)
        = c * (∑ z ∈ boxFinset (0 : Site d) n, green d 0 z * r z)
          + c * s * ∑ z ∈ boxFinset (0 : Site d) n,
            green d 0 z * (greenUnit d hd : Site d → ℝ) z := by
    intro n
    rw [infiniteGreenFieldPartial_boxFinset, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  have htend : Tendsto (fun n : ℕ => infiniteGreenFieldPartial n
        (fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z)) (0 : Site d)) atTop
      (𝓝 (c * 0 + c * s * ‖greenLp d hd (0 : Site d)‖)) := by
    simp only [hsum]
    exact (hr.const_mul c).add ((tendsto_greenPartialSum_greenUnit hd).const_mul (c * s))
  have hex : ∃ L : ℝ, Tendsto (fun n : ℕ => infiniteGreenFieldPartial n
      (fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z)) (0 : Site d)) atTop (𝓝 L) :=
    ⟨_, htend⟩
  rw [infiniteGreenField, dif_pos hex]
  have huniq := tendsto_nhds_unique (Classical.choose_spec hex) htend
  rw [huniq]
  ring

end Sandpile
