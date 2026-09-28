import Sandpile.Support.StarNN
import Sandpile.Support.RectangleTranspose

/-!
# Vertical crossing values from star-graph walks

`rectangle_star_walk_to_nn` (from `Sandpile.Support.StarNN`) turns a star-lattice walk that
stays above a level into a nearest-neighbor walk staying above the level minus the edge
oscillation. This module runs that conversion on `-F` and negates the result back, turning a
star-lattice walk from the bottom row to the top row of a rectangle that stays *below* a level
into a lower bound on the *vertical* crossing value of `-F`
(`verticalCrossingValue_neg_ge_of_star_walk`). The helper `edgeOscillation_neg` records that
`edgeOscillation` is unchanged when `F` is negated.
-/

noncomputable section
namespace Sandpile

/-- `edgeOscillation` is invariant under negating `F`, since `|-F p.1 - -F p.2| = |F p.1 - F p.2|`
for every adjacent pair. -/
lemma edgeOscillation_neg {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (F : V → ℝ) : edgeOscillation G (fun z => -F z) = edgeOscillation G F := by
  classical
  unfold edgeOscillation
  congr 1
  funext p
  split_ifs
  · change |-F p.1 - -F p.2| = |F p.1 - F p.2|
    rw [neg_sub_neg, abs_sub_comm]
  · rfl

/-- If a star-lattice walk `p` from a bottom-row point `a` to a top-row point `b` of the
rectangle stays below `level` throughout, then `-level` minus the edge oscillation of the
rectangle graph is a lower bound for the vertical crossing value of `-F`. The proof replaces `p`
by a nearest-neighbor walk for `-F` via `rectangle_star_walk_to_nn`, then invokes
`le_verticalCrossingValue_of_walk` and `edgeOscillation_neg`. -/
lemma verticalCrossingValue_neg_ge_of_star_walk {w h : ℕ} [Nonempty (planeRectangle w h)]
    (F : planeRectangle w h → ℝ) {a b : planeRectangle w h}
    (p : ((starLatticeGraph 2).induce ((planeRectangle w h) : Set (Site 2))).Walk a b)
    (ha : (a : Site 2) 1 = 0) (hb : (b : Site 2) 1 = h) {level : ℝ}
    (hp : ∀ z ∈ p.support, F z ≤ level) :
    -level - edgeOscillation (rectangleGraph (planeRectangle w h)) F ≤
      verticalCrossingValue w h (fun z => -F z) := by
  obtain ⟨q, hq⟩ := rectangle_star_walk_to_nn (isLatticeRectangle_planeRectangle w h)
    (fun z => -F z) (level := -level) p (fun z hz => neg_le_neg (hp z hz))
  apply le_verticalCrossingValue_of_walk (fun z => -F z) q ha hb
  simpa only [edgeOscillation_neg] using hq

end Sandpile
