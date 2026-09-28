import Sandpile.Support.PlanarLaw

/-! # Planar RSW for Site Percolation

The lattice site specialization of Köhler-Schindler and Tassion,
Crossing probabilities for planar percolation, Theorem 1 and Comment 1
(arXiv 2011.04618v1, pages 1-2), cited at sandpile.tex:400,2064,2218,2235.
The paper places the planar dimension-two-through-four crossing argument in
this RSW framework at sandpile.tex:661-663.

The source uses centered rectangles. Translation invariance gives the
identical statement for rectangles with lower-left corner zero. Integer
aspect ratios and integer half-side lengths are the specialization below.
A planar site's open state is determined by whether its field value is at
least the specified level. Coordinate interchange and reflection, together
with translations, generate exactly the lattice symmetries in the source.

An order isomorphism of [0,1] is equivalently an increasing homeomorphism.
The map depends only on the aspect ratio, before the law, scale and level.
No quantitative rectangle estimate or Gaussian estimate is included in this
input; those consequences require separate proofs.
-/

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
/-- The universal RSW comparison for symmetric, positively associated planar
site percolation, expressed through real field superlevel sets. Assumed,
not proved. -/
def Sandpile.External.PlanarRSW : Prop :=
  ∀ ρ : ℕ, 1 ≤ ρ → ∃ ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
    ∀ μ : Measure (Sandpile.Site 2 → ℝ), ∀ [IsProbabilityMeasure μ],
      Sandpile.IsSymmetricPlanarLaw μ → Sandpile.IsAssociatedPlanarLaw μ →
      ∀ n : ℕ, 1 ≤ n → ∀ level : ℝ,
        (ψ (Sandpile.probabilityInUnitInterval μ
          (Sandpile.planarCrossingEvent (2 * n) (2 * ρ * n) level)) : ℝ) ≤
        μ.real (Sandpile.planarCrossingEvent (2 * ρ * n) (2 * n) level)
-- FROZEN-STATEMENT-END
