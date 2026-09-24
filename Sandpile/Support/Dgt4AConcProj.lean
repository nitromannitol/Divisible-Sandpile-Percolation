/-
An everywhere-defined representative of the rank-one reduction of `sandpile.tex:5270-5271`.

Step 4 of case (a) conditions the Gaussian scenery on the linear functional
`-V_\infty(0)` and asserts that the concentration bound survives the conditioning,
"since conditioning replaces its covariance by a rank-one reduction".  What carries
that sentence is that the reduction is an orthogonal projection, hence a contraction
for the `\ell^2` distance, so a functional Lipschitz for that distance stays Lipschitz
with the same constant after the conditioning.

`residField` of `Support/Dgt4ACondition.lean` is the reduction as the conditioning
needs it, but it is built from `condCoord`, an arbitrary representative of an `L^2`
class, and no representative of an `L^2` class is a contraction at every
configuration.  The projection is therefore rebuilt here at every configuration: the
pairing with the conditioned direction is the limit of the box partial sums where
that limit exists and is zero elsewhere, and the two configurations of a pair at
finite `\ell^2` distance either both have the limit or both do not, because their
partial sums differ by an absolutely convergent series.  The rebuilt projection is
measurable, is almost everywhere `residField`, and is a contraction everywhere.
-/
import Sandpile.Support.Dgt4ACondTail

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The box partial sums of the conditioned direction against a configuration. -/
noncomputable def unitPartial (d : ℕ) (hd : 5 ≤ d) (n : ℕ) (ω : Site d → ℝ) : ℝ :=
  ∑ z ∈ boxFinset (0 : Site d) n, (greenUnit d hd : Site d → ℝ) z * ω z

theorem measurable_unitPartial (hd : 5 ≤ d) (n : ℕ) : Measurable (unitPartial d hd n) := by
  unfold unitPartial
  exact Finset.measurable_sum _ fun z _ => (measurable_pi_apply z).const_mul _

/-- The configurations at which the box partial sums of the conditioned direction
converge. -/
def unitConv (d : ℕ) (hd : 5 ≤ d) : Set (Site d → ℝ) :=
  {ω | ∃ L : ℝ, Tendsto (fun n => unitPartial d hd n ω) atTop (𝓝 L)}

theorem measurableSet_unitConv (hd : 5 ≤ d) : MeasurableSet (unitConv d hd) := by
  exact MeasureTheory.measurableSet_exists_tendsto (fun n => measurable_unitPartial hd n)

/-- The pairing of a configuration with the conditioned direction, defined at every
configuration. -/
noncomputable def unitPairing (d : ℕ) (hd : 5 ≤ d) : (Site d → ℝ) → ℝ :=
  Set.indicator (unitConv d hd) fun ω => limUnder atTop fun n => unitPartial d hd n ω

theorem unitPairing_eq_of_tendsto (hd : 5 ≤ d) {ω : Site d → ℝ} {L : ℝ}
    (h : Tendsto (fun n => unitPartial d hd n ω) atTop (𝓝 L)) :
    unitPairing d hd ω = L := by
  have hmem : ω ∈ unitConv d hd := ⟨L, h⟩
  rw [unitPairing, Set.indicator_of_mem hmem, h.limUnder_eq]

theorem unitPairing_of_notMem (hd : 5 ≤ d) {ω : Site d → ℝ} (hω : ω ∉ unitConv d hd) :
    unitPairing d hd ω = 0 := by
  rw [unitPairing, Set.indicator_of_notMem hω]

theorem tendsto_unitPartial_unitPairing (hd : 5 ≤ d) {ω : Site d → ℝ}
    (hω : ω ∈ unitConv d hd) :
    Tendsto (fun n => unitPartial d hd n ω) atTop (𝓝 (unitPairing d hd ω)) := by
  obtain ⟨L, hL⟩ := hω
  rw [unitPairing_eq_of_tendsto hd hL]
  exact hL

theorem measurable_unitPairing (hd : 5 ≤ d) : Measurable (unitPairing d hd) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n => (unitConv d hd).indicator (unitPartial d hd n))
    (fun n => (measurable_unitPartial hd n).indicator (measurableSet_unitConv hd)) ?_
  refine tendsto_pi_nhds.2 fun ω => ?_
  by_cases hω : ω ∈ unitConv d hd
  · refine (tendsto_unitPartial_unitPairing hd hω).congr fun n => ?_
    rw [Set.indicator_of_mem hω]
  · rw [unitPairing_of_notMem hd hω]
    refine tendsto_const_nhds.congr fun n => ?_
    rw [Set.indicator_of_notMem hω]

/-- The rank-one reduction, at every configuration. -/
noncomputable def projUnit (d : ℕ) (hd : 5 ≤ d) (ω : Site d → ℝ) : Site d → ℝ :=
  fun z => ω z - unitPairing d hd ω * (greenUnit d hd : Site d → ℝ) z

theorem measurable_projUnit (hd : 5 ≤ d) : Measurable (projUnit d hd) := by
  refine measurable_pi_iff.2 fun z => ?_
  exact (measurable_pi_apply z).sub ((measurable_unitPairing hd).mul_const _)

theorem ae_unitPairing_eq_condCoord (hd : 5 ≤ d) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)), unitPairing d hd ω = condCoord d hd ω := by
  have hcoe : ∀ z : Site d, (greenUnit d hd : Site d → ℝ) z
      = ‖greenLp d hd (0 : Site d)‖⁻¹ * green d 0 z := by
    intro z
    rw [greenUnit, lp.coeFn_smul, Pi.smul_apply, coeFn_greenLp, smul_eq_mul]
  have hsmul : LatticeProb.gaussIso (greenUnit d hd)
      = ‖greenLp d hd (0 : Site d)‖⁻¹ • LatticeProb.gaussIso (greenLp d hd (0 : Site d)) := by
    rw [greenUnit, map_smul]
  filter_upwards [ae_tendsto_greenPartialSum hd (0 : Site d),
    Lp.coeFn_smul (‖greenLp d hd (0 : Site d)‖⁻¹)
      (LatticeProb.gaussIso (greenLp d hd (0 : Site d)))] with ω h1 h2
  have hpart : (fun n => unitPartial d hd n ω)
      = fun n => ‖greenLp d hd (0 : Site d)‖⁻¹
        * ∑ z ∈ boxFinset (0 : Site d) n, green d 0 z * ω z := by
    funext n
    rw [unitPartial, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [hcoe z]; ring
  have htend : Tendsto (fun n => unitPartial d hd n ω) atTop
      (𝓝 (‖greenLp d hd (0 : Site d)‖⁻¹
        * ⇑(LatticeProb.gaussIso (greenLp d hd (0 : Site d))) ω)) := by
    rw [hpart]
    exact h1.const_mul _
  rw [unitPairing_eq_of_tendsto hd htend, condCoord, hsmul, h2, Pi.smul_apply, smul_eq_mul]

theorem ae_projUnit_eq_residField (hd : 5 ≤ d) :
    projUnit d hd =ᵐ[LatticeProb.gaussLaw (Site d)] residField d hd := by
  filter_upwards [ae_unitPairing_eq_condCoord hd] with ω hω
  funext z
  rw [projUnit, residField, hω]

end Sandpile
