import Sandpile.Support.LinTestedField
import Sandpile.Support.LinScaledPairing
import Sandpile.Support.SceneryBridge
import Sandpile.Support.Stationary
import Sandpile.Support.Iterate
import Sandpile.Support.ContDGT4Membrane

/-!
# The tested field is the scaled lattice pairing

The tested field IS the scaled lattice pairing.

`sandpile.tex:5665-5668` writes `F_R = ∑_x a_R(x) u_{n_R}(x)` with
`a_R(x) = R^{(d-4)/2} φ_R(x)` and `φ_R(x)` the mass of the test function on the
cell of `x`. Since `φ` has compact support, the pairing
`R^{(d-4)/2}(u_{n_R})^{(R)}(φ)` is exactly that finite sum, and the centring
constant `R^{(d-4)/2}(E u_{n_R}(0))^{(R)}(φ)` is exactly `E F_R`, because the
mean odometer does not depend on the site.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The scaled lattice pairing of any lattice field is the finite sum of its values
against the weights `a_R(x) = R^{(d-4)/2} φ_R(x)` of `sandpile.tex:5660-5663`. -/
theorem scaled_latticePairing_eq_weighted_sum (R : ℝ) (f : Site d → ℝ) (φ : Space d → ℝ)
    (hφ : Integrable φ) (s : Finset (Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R f φ
      = ∑ x ∈ s, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) * f x := by
  rw [Sandpile.Support.latticePairing_eq_sum R f φ hφ s hs, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The scaled pairing of the odometer IS the tested field `F_R` of the
linearization, read in the scenery. -/
theorem scaled_latticePairing_odometer_eq_testedField (R : ℝ) (nn : ℕ) (σ : Site d → ℝ)
    (φ : Space d → ℝ) (hφ : Integrable φ) (s : Finset (Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    R ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing R (fun x => Sandpile.odometer σ nn x) φ
      = testedField s
          (fun x => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) nn
          (Sandpile.scenery d σ) := by
  rw [scaled_latticePairing_eq_weighted_sum R (fun x => Sandpile.odometer σ nn x) φ hφ s hs]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  exact congrFun (odometer_eq_odometerOf σ nn) x

/-- The scaled pairing of the constant mean odometer is the total weight times
that mean. -/
theorem scaled_latticePairing_const_eq (R : ℝ) (m : ℝ) (φ : Space d → ℝ)
    (hφ : Integrable φ) (s : Finset (Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R (fun _ => m) φ
      = (∑ x ∈ s, R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) * m := by
  rw [scaled_latticePairing_eq_weighted_sum R (fun _ => m) φ hφ s hs, Finset.sum_mul]

/-- The mean of the tested field is the total weight times the mean odometer at
the origin, by stationarity. -/
theorem integral_testedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (s : Finset (Site d)) (a : Site d → ℝ) (nn : ℕ) :
    ∫ ζ, testedField s a nn ζ ∂(LatticeProb.iidLaw d ν)
      = (∑ x ∈ s, a x) * ∫ ζ, odometerOf ζ nn 0 ∂(LatticeProb.iidLaw d ν) := by
  show ∫ ζ, ∑ x ∈ s, a x * odometerOf ζ nn x ∂(LatticeProb.iidLaw d ν) = _
  rw [integral_finsetSum s fun x _ => (integrable_odometerOf d ν hpos nn x).const_mul (a x)]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by
    rw [integral_const_mul, integral_odometerOf_eq d ν nn x]

/-- The scaled pairing of the constant `E u_{n_R}(0)` is the mean of the tested
field: the two centring terms of `eq:dgt4-linearization-from-paths` agree. -/
theorem scaled_latticePairing_meanOdometer_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (hpos : Integrable (fun z => max z 0) ν) (R : ℝ) (nn : ℕ)
    (φ : Space d → ℝ) (hφ : Integrable φ) (s : Finset (Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun _ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) nn) φ
      = ∫ ζ, testedField s
          (fun x => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) nn ζ
          ∂(LatticeProb.iidLaw d ν) := by
  rw [scaled_latticePairing_const_eq R _ φ hφ s hs,
    integral_testedField ν hpos s _ nn, meanOdometer_centeredMassLaw_eq d ν hd nn]

/-- The weighted linear field `∑_{j<N} q_j P^jζ` at a site is a finite sum over
the box of radius `N`. -/
theorem sum_weight_avg_iterate_eq (N : ℕ) (q : ℕ → ℝ) (ζ : Site d → ℝ) (x : Site d)
    (t : Finset (Site d)) (ht : boxFinset x N ⊆ t) :
    ∑ j ∈ Finset.range N, q j * (avg^[j] ζ) x
      = ∑ z ∈ t, (∑ j ∈ Finset.range N, q j * heatKernel d j x z) * ζ z := by
  classical
  have hterm : ∀ j ∈ Finset.range N, q j * (avg^[j] ζ) x
      = ∑ z ∈ t, q j * heatKernel d j x z * ζ z := by
    intro j hj
    have hjN : j ≤ N := Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Finset.mem_range.1 hj))
    rw [avg_iterate j ζ x, tsum_eq_sum (s := t) ?_, Finset.mul_sum]
    · exact Finset.sum_congr rfl fun z _ => by ring
    · intro z hz
      have hker : heatKernel d j x z = 0 := by
        by_contra hne
        exact hz (ht (mem_boxFinset (le_trans (heatKernel_support j x hne) hjN)))
      simp [hker]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_mul]

/-- **The scaled pairing of the weighted linear field is a linear functional of
the scenery on the sites the tested field reads**, with the coefficients
`∑_x a_R(x) ∑_{j<N} q_j p_j(x,z)` of `sandpile.tex:5820-5830`. -/
theorem scaled_latticePairing_weighted_eq (R : ℝ) (N : ℕ) (q : ℕ → ℝ) (ζ : Site d → ℝ)
    (φ : Space d → ℝ) (hφ : Integrable φ) (s : Finset (Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => ∑ j ∈ Finset.range N, q j * (avg^[j] ζ) x) φ
      = ∑ z ∈ testedSites s N,
          (∑ x ∈ s, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) *
            ∑ j ∈ Finset.range N, q j * heatKernel d j x z) * ζ z := by
  classical
  rw [scaled_latticePairing_eq_weighted_sum R _ φ hφ s hs]
  have hterm : ∀ x ∈ s,
      (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) *
          (∑ j ∈ Finset.range N, q j * (avg^[j] ζ) x)
        = ∑ z ∈ testedSites s N,
            (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) *
              (∑ j ∈ Finset.range N, q j * heatKernel d j x z) * ζ z := by
    intro x hx
    have hsub : boxFinset x N ⊆ testedSites s N := fun z hz =>
      Finset.mem_biUnion.2 ⟨x, hx, hz⟩
    rw [sum_weight_avg_iterate_eq N q ζ x _ hsub, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_mul]

/-- **The frozen integrand of `eq:dgt4-linearization-from-paths` in the
vocabulary of the tested field.**  The three pairings of the difference are the
tested field, its mean and the linear functional of the scenery whose
coefficients are `∑_x a_R(x) ∑_{j<n_R} q_{R,j} p_j(x,z)`. -/
theorem frozen_integrand_eq_testedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (hpos : Integrable (fun z => max z 0) ν)
    (R : ℝ) (N : ℕ) (q : ℕ → ℝ) (σ : Site d → ℝ)
    (φ : Space d → ℝ) (hφ : Integrable φ) {Lb : ℝ}
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ Lb)
    (s : Finset (Site d)) (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ N x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) N -
          ∑ j ∈ Finset.range N, q j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ
      = testedField s
            (fun x => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) N
            (Sandpile.scenery d σ)
        - (∫ ζ, testedField s
            (fun x => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) N ζ
            ∂(LatticeProb.iidLaw d ν))
        - ∑ z ∈ testedSites s N,
            (∑ x ∈ s, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) *
              ∑ j ∈ Finset.range N, q j * heatKernel d j x z) *
              Sandpile.scenery d σ z := by
  have hsplit : Sandpile.Continuum.latticePairing R
      (fun x => Sandpile.odometer σ N x -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) N -
        ∑ j ∈ Finset.range N, q j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ
      = Sandpile.Continuum.latticePairing R (fun x => Sandpile.odometer σ N x) φ
        - Sandpile.Continuum.latticePairing R
            (fun _ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) N) φ
        - Sandpile.Continuum.latticePairing R
            (fun x => ∑ j ∈ Finset.range N,
              q j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ := by
    rw [Sandpile.Support.latticePairing_sub R
        (fun x => Sandpile.odometer σ N x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) N)
        (fun x => ∑ j ∈ Finset.range N,
          q j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ hφ hsupp,
      Sandpile.Support.latticePairing_sub R (fun x => Sandpile.odometer σ N x)
        (fun _ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) N) φ hφ hsupp]
  rw [hsplit, mul_sub, mul_sub,
    scaled_latticePairing_odometer_eq_testedField R N σ φ hφ s hs,
    scaled_latticePairing_meanOdometer_eq ν hd hpos R N φ hφ s hs,
    scaled_latticePairing_weighted_eq R N q (Sandpile.scenery d σ) φ hφ s hs]

/-- An integral of a functional of the scenery is the same under the mass law and
under the i.i.d. law of the scenery. -/
theorem integral_scenery_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (G : (Site d → ℝ) → ℝ) (hG : AEStronglyMeasurable G (LatticeProb.iidLaw d ν)) :
    ∫ σ, G (Sandpile.scenery d σ) ∂(Sandpile.centeredMassLaw d ν)
      = ∫ ζ, G ζ ∂(LatticeProb.iidLaw d ν) := by
  have h := integral_map (μ := Sandpile.centeredMassLaw d ν) (φ := Sandpile.scenery d) (f := G)
    (measurable_scenery d).aemeasurable
    (by rw [map_scenery_centeredMassLaw d ν hd]; exact hG)
  rw [map_scenery_centeredMassLaw d ν hd] at h
  exact h.symm

/-- **The second moment of the frozen integrand of
`eq:dgt4-linearization-from-paths` is the second moment Step 2 bounds.** -/
theorem integral_sq_frozen_eq_testedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (hpos : Integrable (fun z => max z 0) ν)
    (R : ℝ) (N : ℕ) (q : ℕ → ℝ)
    (φ : Space d → ℝ) (hφ : Integrable φ) {Lb : ℝ}
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ Lb)
    (s : Finset (Site d)) (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    ∫ σ, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ N x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) N -
          ∑ j ∈ Finset.range N, q j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
        ∂(Sandpile.centeredMassLaw d ν)
      = ∫ ζ, (testedField s
            (fun x => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) N ζ
          - (∫ η, testedField s
              (fun x => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) N η
              ∂(LatticeProb.iidLaw d ν))
          - ∑ z ∈ testedSites s N,
              (∑ x ∈ s, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) *
                ∑ j ∈ Finset.range N, q j * heatKernel d j x z) * ζ z) ^ 2
        ∂(LatticeProb.iidLaw d ν) := by
  classical
  set a : Site d → ℝ :=
    fun x => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x with ha
  set c : Site d → ℝ := fun z => ∑ x ∈ s, a x *
    ∑ j ∈ Finset.range N, q j * heatKernel d j x z with hc
  set G : (Site d → ℝ) → ℝ := fun ζ =>
    (testedField s a N ζ - (∫ η, testedField s a N η ∂(LatticeProb.iidLaw d ν))
      - ∑ z ∈ testedSites s N, c z * ζ z) ^ 2 with hG
  have hGm : Measurable G := by
    refine (((measurable_testedField s a N).sub measurable_const).sub ?_).pow_const 2
    exact Finset.measurable_sum _ fun z _ => measurable_const.mul (measurable_pi_apply z)
  have hpt : ∀ σ : Site d → ℝ,
      (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ N x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) N -
          ∑ j ∈ Finset.range N, q j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
        = G (Sandpile.scenery d σ) := by
    intro σ
    rw [hG]
    exact congrArg (fun t => t ^ 2)
      (frozen_integrand_eq_testedField ν hd hpos R N q σ φ hφ hsupp s hs)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_scenery_eq ν hd G hGm.aestronglyMeasurable

end Sandpile
