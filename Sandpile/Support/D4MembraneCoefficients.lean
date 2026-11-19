import Sandpile.Support.D4DefectOmega
import Sandpile.Support.FiniteCoord
import Sandpile.External.MembraneScalingFour

/-!
# Coefficients of the four-dimensional membrane pairing

A compactly supported `ω`-shifted test function meets finitely many lattice
cells. Pairing either the finite-time Green kernel or the potential kernel with
the cell masses gives a coefficient at each scenery site. Their difference is
the paired defect, and the finite-time membrane pairing is the corresponding
finite weighted sum of scenery variables.
-/

open MeasureTheory

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The coefficient obtained by pairing a lattice kernel with cell masses. -/
noncomputable def cellKernelCoeff (R : ℝ) (ψ : Space 4 → ℝ)
    (s : Finset (Site 4)) (K : Site 4 → Site 4 → ℝ) (y : Site 4) : ℝ :=
  ∑ x ∈ s, K x y * cellMass R ψ x

/-- The paired defect is the difference of the finite-time and potential
kernel coefficients. -/
theorem membraneDefect_eq_coeff_sub {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (R : ℝ) (t : ℕ) (s : Finset (Site 4))
    (hint : Integrable (omegaShift D w φ))
    (hs : ∀ z, omegaShift D w φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s)
    (y : Site 4) :
    Sandpile.External.membraneDefect R t D w φ y =
      cellKernelCoeff R (omegaShift D w φ) s (greenTime 4 t) y -
        cellKernelCoeff R (omegaShift D w φ) s (potentialKernel 4) y := by
  rw [Sandpile.External.membraneDefect, Sandpile.Continuum.omegaRep]
  change latticePairing R (fun x => greenTime 4 t x y - potentialKernel 4 x y)
    (omegaShift D w φ) = _
  rw [latticePairing_eq_sum R _ _ hint s hs, cellKernelCoeff, cellKernelCoeff,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The finite-time coefficient vanishes outside a set containing the
walk-reachable boxes of all cells. -/
theorem cellKernelCoeff_greenTime_eq_zero {R : ℝ} {ψ : Space 4 → ℝ}
    {s s' : Finset (Site 4)} {t : ℕ}
    (hs : ∀ x ∈ s, Sandpile.boxFinset x t ⊆ s') {y : Site 4} (hy : y ∉ s') :
    cellKernelCoeff R ψ s (greenTime 4 t) y = 0 := by
  refine Finset.sum_eq_zero fun x hx => ?_
  have hzero : greenTime 4 t x y = 0 := by
    by_contra hne
    exact hy (hs x hx (Sandpile.mem_boxFinset (greenTime_support t x hne)))
  rw [hzero, zero_mul]

/-- The `ω`-paired membrane field is a finite linear functional of the scenery,
with the finite-time kernel coefficients. -/
theorem omegaRep_membrane_eq_sum {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (R : ℝ) (t : ℕ) (ζ : Site 4 → ℝ) (s s' : Finset (Site 4))
    (hint : Integrable (omegaShift D w φ))
    (hs : ∀ z, omegaShift D w φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s)
    (hs' : ∀ x ∈ s, Sandpile.boxFinset x t ⊆ s') :
    omegaRep D w (latticePairing R (membrane ζ t)) φ =
      ∑ y ∈ s', cellKernelCoeff R (omegaShift D w φ) s (greenTime 4 t) y * ζ y := by
  rw [omegaRep]
  change latticePairing R (membrane ζ t) (omegaShift D w φ) = _
  rw [latticePairing_eq_sum R _ _ hint s hs]
  have h : ∀ x ∈ s, membrane ζ t x * cellMass R (omegaShift D w φ) x =
      ∑ y ∈ s', greenTime 4 t x y * cellMass R (omegaShift D w φ) x * ζ y := by
    intro x hx
    rw [membrane_eq_sum_siteEnum (hs' x hx) ζ]
    rw [show (∑ i : Fin s'.card, greenTime 4 t x (siteEnum s' i) *
      ζ (siteEnum s' i)) = ∑ y ∈ s', greenTime 4 t x y * ζ y from
        sum_siteEnum s' (fun y => greenTime 4 t x y * ζ y), Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [cellKernelCoeff, Finset.sum_mul]

end Sandpile.Support
