import Sandpile.External.RSW.BondSymmetry

/-!
# Centered rectangle crossings

The centered rectangle with integer half-side lengths is an integer translate of the
corresponding rectangle based at the origin. Symmetry identifies their crossing probabilities.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- Shifting a site by the half-side vector identifies a centered box with the corresponding
origin-based box. -/
theorem mem_shifted_planeRectangle_iff (m n : ℕ) (z : Site 2) :
    z + ![(m : ℤ), (n : ℤ)] ∈ planeRectangle (2 * m) (2 * n) ↔
      -(m : ℤ) ≤ z 0 ∧ z 0 ≤ m ∧ -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n := by
  rw [mem_planeRectangle]
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- A bond crossing of `[-m,m] × [-n,n]`, obtained by translating the origin-based event. -/
def centeredBondCrossingEvent (m n : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  (fun ω : Sym2 (Site 2) → Bool =>
    ω ∘ Sym2.map (fun z => z + (- ![(m : ℤ), (n : ℤ)]))) ⁻¹'
      bondCrossingEvent (2 * m) (2 * n)

/-- The centered bond crossing event is measurable. -/
theorem measurableSet_centeredBondCrossingEvent (m n : ℕ) :
    MeasurableSet (centeredBondCrossingEvent m n) := by
  exact (measurableSet_bondCrossingEvent (2 * m) (2 * n)).preimage
    (Measurable.of_eval (fun e => measurable_pi_apply
      (Sym2.map (fun z => z + (- ![(m : ℤ), (n : ℤ)])) e)))

/-- Translating a crossing to a centered box preserves its probability under a symmetric
field's induced bond law. -/
theorem fieldBondLaw_centeredCrossing (μ : Measure (Site 2 → ℝ))
    (hμ : IsSymmetricPlanarLaw μ) (level : ℝ) (m n : ℕ) :
    (fieldBondLaw μ level).real (centeredBondCrossingEvent m n) =
      (fieldBondLaw μ level).real (bondCrossingEvent (2 * m) (2 * n)) := by
  exact ((fieldBondLaw_symmetric μ hμ level).1 (- ![(m : ℤ), (n : ℤ)])).measureReal_preimage
    (measurableSet_bondCrossingEvent (2 * m) (2 * n)).nullMeasurableSet

/-- The centered bond crossing probability equals the origin-based field crossing probability
when the rectangle has positive width. -/
theorem fieldBondLaw_centeredCrossing_eq_field (μ : Measure (Site 2 → ℝ))
    (hμ : IsSymmetricPlanarLaw μ) (level : ℝ) (m n : ℕ) (hm : 0 < m) :
    (fieldBondLaw μ level).real (centeredBondCrossingEvent m n) =
      μ.real (planarCrossingEvent (2 * m) (2 * n) level) :=
  (fieldBondLaw_centeredCrossing μ hμ level m n).trans
    (fieldBondLaw_crossing μ level (2 * m) (2 * n) (by omega))

end Sandpile.External.RSW
