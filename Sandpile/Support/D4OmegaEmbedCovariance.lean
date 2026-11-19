import Sandpile.Support.D4CenteredCovariance
import Sandpile.Support.D4OmegaEnergy

/-!
# Covariance of the centered membrane embedding

The covariance of two values of the piecewise-constant membrane embedding,
after subtracting its weighted spatial average, is the centered doubled heat
kernel.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The centered embedding is a field value minus a finite weighted average. -/
theorem omegaEmbed_eq_sub_cellMass {d : ℕ} (R L : ℝ) (w : Space d → ℝ)
    (hw : Integrable w) (hL : ∀ z, w z ≠ 0 → ‖z‖ ≤ L)
    (f : Site d → ℝ) (z : Space d) :
    omegaEmbed R w f z = f (fun i => ⌊R * z i⌋) -
      ∑ a ∈ supportBox d R L, cellMass R w a * f a := by
  have hs : ∀ z : Space d, w z ≠ 0 →
      (fun i => ⌊R * z i⌋) ∈ supportBox d R L :=
    fun z hz => floor_mem_boxFinset R z (hL z hz)
  have h := latticePairing_eq_sum R f w hw (supportBox d R L) hs
  change (∫ u : Space d, embed R f u * w u) = _ at h
  rw [omegaEmbed, h]
  simp only [embed]
  congr 1
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The covariance of the centered membrane embedding is the centered
covariance kernel of its lattice values. -/
theorem covariance_omegaEmbed_membrane {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (R L : ℝ) (w : Space d → ℝ) (hw : Integrable w)
    (hL : ∀ z, w z ≠ 0 → ‖z‖ ≤ L) (t : ℕ) (u v : Space d) :
    let K : Site d → Site d → ℝ := fun x y =>
      variance id ν * ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
        heatKernel d (a + b) x y
    let x : Site d := fun i => ⌊R * u i⌋
    let y : Site d := fun i => ⌊R * v i⌋
    let s := supportBox d R L
    let m := cellMass R w
    covariance (fun σ => omegaEmbed R w (membrane (scenery d σ) t) u)
      (fun σ => omegaEmbed R w (membrane (scenery d σ) t) v) (centeredMassLaw d ν) =
      K x y - (∑ a ∈ s, m a * K x a) - (∑ a ∈ s, m a * K a y) +
        (∑ a ∈ s, ∑ b ∈ s, m a * m b * K a b) := by
  dsimp only
  have hX (x : Site d) : MemLp (fun σ => membrane (scenery d σ) t x) 2
      (centeredMassLaw d ν) := by
    simpa only [weightedField_one_eq_membrane] using
      memLp_two_weightedField_mass ν hsq hd (fun _ => 1) t x
  simp_rw [omegaEmbed_eq_sub_cellMass R L w hw hL]
  rw [covariance_sub_weighted_average (centeredMassLaw d ν)
    (fun x σ => membrane (scenery d σ) t x) hX]
  simp_rw [covariance_membrane_mass hd ν hsq]

/-- Nonnegative unit-mass averaging functions give finite probability weights
on the cells meeting their support. -/
theorem cellMass_probability {d : ℕ} (R L : ℝ) (w : Space d → ℝ)
    (hw : Integrable w) (hL : ∀ z, w z ≠ 0 → ‖z‖ ≤ L)
    (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∫ z, w z = 1) :
    (∑ a ∈ supportBox d R L, cellMass R w a = 1) ∧
      ∀ a ∈ supportBox d R L, 0 ≤ cellMass R w a := by
  constructor
  · rw [sum_cellMass_eq_integral R w hw (supportBox d R L)
      (fun z hz => floor_mem_boxFinset R z (hL z hz)), hw1]
  · intro a _
    exact integral_nonneg fun z => hw0 z

/-- The centered membrane covariance is bounded by four weighted averages of
the error in its uncentered covariance kernel after subtracting a constant. -/
theorem abs_covariance_omegaEmbed_membrane_le {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (R L : ℝ) (w : Space d → ℝ) (hw : Integrable w)
    (hL : ∀ z, w z ≠ 0 → ‖z‖ ≤ L) (hw0 : ∀ z, 0 ≤ w z)
    (hw1 : ∫ z, w z = 1) (t : ℕ) (u v : Space d) (A : ℝ) :
    let K : Site d → Site d → ℝ := fun x y =>
      variance id ν * ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
        heatKernel d (a + b) x y
    let x : Site d := fun i => ⌊R * u i⌋
    let y : Site d := fun i => ⌊R * v i⌋
    let s := supportBox d R L
    let m := cellMass R w
    |covariance (fun σ => omegaEmbed R w (membrane (scenery d σ) t) u)
      (fun σ => omegaEmbed R w (membrane (scenery d σ) t) v) (centeredMassLaw d ν)| ≤
      |K x y - A| + (∑ a ∈ s, m a * |K x a - A|) +
        (∑ a ∈ s, m a * |K a y - A|) +
        (∑ a ∈ s, ∑ b ∈ s, m a * m b * |K a b - A|) := by
  dsimp only
  rw [covariance_omegaEmbed_membrane hd ν hsq R L w hw hL t u v]
  exact abs_centeredKernel_le _ _ (cellMass_probability R L w hw hL hw0 hw1).1
    (cellMass_probability R L w hw hL hw0 hw1).2
    (fun x y => variance id ν * ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
      heatKernel d (a + b) x y) A (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋)

end Sandpile.Support
