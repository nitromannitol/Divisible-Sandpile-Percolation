import Sandpile.Support.LinJacobianInterMoments
import Sandpile.Support.LinTested

/-!
# The tested intersection moments, specialized to every starting pair

`eq:dgt4-tested-intersection-moments` (`sandpile.tex:5703-5709`) in the form Step 1 of
`lem:dgt4-linearization-from-survival` consumes it: the two tested moments of the REAL
intersection count, integrated against the law of the two walks.

`Support/LinTested.lean` proves the two displays with the count in `ℝ≥0∞` and the
expectations as iterated lower integrals; `Support/LinJacobianInterMoments.lean` converts
one weighted sum at a time. The first moment is finite for every pair of starting points
in `d ≥ 5`, which is what makes the real count a genuine majorant almost everywhere and
both moments genuine Bochner integrals.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- In `d ≥ 5` the first intersection moment is finite for every pair of
starting points. -/
theorem lintegral_interCount_ne_top [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh) (x y : Site d) :
    (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y
      ∂(walkLaw d y) ∂(walkLaw d x)) ≠ ⊤ := by
  obtain ⟨C, _, hC⟩ := lintegral_interCount_le hd hGreen
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC x y)

/-- In `d ≥ 5` the second intersection moment is finite for every pair of
starting points. -/
theorem lintegral_interCount_sq_ne_top [NeZero d] (hd : 5 ≤ d)
    (hInter : Sandpile.External.IntersectionSecondMoment) (x y : Site d) :
    (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2
      ∂(walkLaw d y) ∂(walkLaw d x)) ≠ ⊤ := by
  obtain ⟨C, _, hC⟩ := hInter d hd
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC x y)

/-- **The hypothesis `hsumI` of Step 1 for every pair of starting points.** -/
theorem ae_sum_indicator_le_interCountReal_of_green [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh) (t : Finset ℕ) (x y : Site d) :
    ∀ᵐ p ∂(walkPairLaw d x y),
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0)
        ≤ interCountReal p.1 p.2 :=
  ae_sum_indicator_le_interCountReal x y (lintegral_interCount_ne_top hd hGreen x y) t

/-- **The hypothesis `hint1` of Step 1 for every pair of starting points.** -/
theorem integrable_interCountReal_of_green [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh) (x y : Site d) :
    Integrable (fun p => interCountReal p.1 p.2) (walkPairLaw d x y) :=
  integrable_interCountReal x y (lintegral_interCount_ne_top hd hGreen x y)

/-- **The hypothesis `hint2` of Step 1 for every pair of starting points.** -/
theorem integrable_interCountReal_sq_of_inter [NeZero d] (hd : 5 ≤ d)
    (hInter : Sandpile.External.IntersectionSecondMoment) (x y : Site d) :
    Integrable (fun p => (interCountReal p.1 p.2) ^ 2) (walkPairLaw d x y) :=
  integrable_interCountReal_sq x y (lintegral_interCount_sq_ne_top hd hInter x y)

/-- **The first tested intersection moment of
`eq:dgt4-tested-intersection-moments` in the Bochner vocabulary**, the
hypothesis `hI1` of Step 1. -/
theorem exists_sum_tested_integral_interCountReal_le [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (φ : Sandpile.Continuum.Space d → ℝ) (Cφ L : ℝ) (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L)
    (hb : ∀ z, |φ z| ≤ Cφ) (hint : Integrable φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
        (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x|) *
          (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ y|) *
          (∫ p, interCountReal p.1 p.2 ∂(walkPairLaw d x y)) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_tested_first_moment_le hd hGreen φ Cφ L hCφ hL hb hint
  refine ⟨C, hC0, fun R hR => ?_⟩
  have hrw : ∀ x y : Site d,
      (∫ p, interCountReal p.1 p.2 ∂(walkPairLaw d x y))
        = (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y
            ∂(walkLaw d y) ∂(walkLaw d x)).toReal := fun x y =>
    integral_interCountReal_eq x y (lintegral_interCount_ne_top hd hGreen x y)
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hrw x y]]
  exact sum_sum_toReal_le_of_ennreal _
    (fun x y => (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x|) *
      (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ y|))
    (fun x y => by positivity)
    (fun x y => ∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y
      ∂(walkLaw d y) ∂(walkLaw d x)) C hC0 (hC R hR)

/-- **The second tested intersection moment of
`eq:dgt4-tested-intersection-moments` in the Bochner vocabulary**, the
hypothesis `hI2` of Step 1. -/
theorem exists_sum_tested_integral_interCountReal_sq_le [NeZero d] (hd : 5 ≤ d)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (φ : Sandpile.Continuum.Space d → ℝ) (Cφ L : ℝ) (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L)
    (hb : ∀ z, |φ z| ≤ Cφ) (hint : Integrable φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
        (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x|) *
          (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ y|) *
          (∫ p, (interCountReal p.1 p.2) ^ 2 ∂(walkPairLaw d x y)) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_tested_second_moment_le hd hInter φ Cφ L hCφ hL hb hint
  refine ⟨C, hC0, fun R hR => ?_⟩
  have hrw : ∀ x y : Site d,
      (∫ p, (interCountReal p.1 p.2) ^ 2 ∂(walkPairLaw d x y))
        = (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2
            ∂(walkLaw d y) ∂(walkLaw d x)).toReal := fun x y =>
    integral_interCountReal_sq_eq x y (lintegral_interCount_sq_ne_top hd hInter x y)
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hrw x y]]
  exact sum_sum_toReal_le_of_ennreal _
    (fun x y => (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x|) *
      (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ y|))
    (fun x y => by positivity)
    (fun x y => ∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2
      ∂(walkLaw d y) ∂(walkLaw d x)) C hC0 (hC R hR)

end Sandpile
