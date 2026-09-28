import Sandpile.Support.Dgt4AShiftLip

/-!
# Measurability of the conditioned Green field

Measurability of the conditioned field in the residual, which is what makes the comparison of
Step 2 (`sandpile.tex:5125-5131`) an integral comparison at all. The box partial sums are finite
sums of coordinates, hence measurable in the residual; the field itself is their limit wherever
that limit exists, and `Support/Dgt4AConditionSite.lean` shows that the limit exists almost
surely under the law of the residual field. So the field is almost everywhere measurable, by the
same route that `Support/LinGaussBridge.lean` uses for the i.i.d. scenery.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The box partial sums of the conditioned field are measurable in the residual. -/
theorem measurable_infiniteGreenFieldPartial_condScenery (hd : 5 ≤ d) (c s : ℝ) (x : Site d)
    (m : ℕ) :
    Measurable (fun r : Site d → ℝ =>
      infiniteGreenFieldPartial m (condScenery d hd c r s) x) := by
  have hrw : (fun r : Site d → ℝ => infiniteGreenFieldPartial m (condScenery d hd c r s) x)
      = fun r : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) m,
        green d x z * (c * (r z + s * (greenUnit d hd : Site d → ℝ) z)) := by
    funext r
    rw [infiniteGreenFieldPartial_boxFinset_site]
    exact Finset.sum_congr rfl fun z _ => by rw [condScenery_apply]
  rw [hrw]
  refine Finset.measurable_sum _ fun z _ => ?_
  have h1 : Measurable fun r : Site d → ℝ => r z + s * (greenUnit d hd : Site d → ℝ) z :=
    (measurable_pi_apply z).add measurable_const
  exact (h1.const_mul c).const_mul (green d x z)

/-- The conditioned field is almost everywhere measurable in the residual. -/
theorem aemeasurable_infiniteGreenField_condScenery (hd : 5 ≤ d) (c s : ℝ) (x : Site d) :
    AEMeasurable (fun r : Site d → ℝ => infiniteGreenField (condScenery d hd c r s) x)
      ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) := by
  refine aemeasurable_of_tendsto_metrizable_ae'
    (fun m => (measurable_infiniteGreenFieldPartial_condScenery hd c s x m).aemeasurable) ?_
  filter_upwards [ae_exists_tendsto_greenPartialSum_resid hd x] with r hr
  obtain ⟨L, hL⟩ := hr
  have htend := tendsto_infiniteGreenFieldPartial_shift hd c x hL s
  have hex : ∃ M : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m (condScenery d hd c r s) x) atTop (𝓝 M) :=
    ⟨_, htend⟩
  rw [infiniteGreenField, dif_pos hex]
  exact Classical.choose_spec hex

end Sandpile
