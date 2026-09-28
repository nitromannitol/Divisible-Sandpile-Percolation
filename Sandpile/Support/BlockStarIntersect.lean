import Sandpile.Support.BlockGeometry
import Sandpile.Support.RectangleIntersection

/-!
# The planar intersection of a crossing star

The planar intersection step of the block-adjacency argument: a left-right nearest-neighbour walk
and a bottom-top nearest-neighbour walk of the same lattice rectangle must share a site. The proof
reduces the bottom-top walk to the nearest-neighbour star of `nnWalkToStar` and applies
`rectangle_nn_star_intersect` to locate the shared site.
-/

open scoped NNReal
noncomputable section
namespace Sandpile

/-- A left-right nearest-neighbour walk and a bottom-top nearest-neighbour
walk of the same lattice rectangle share a site. -/
theorem nn_lr_tb_intersect {w h : ℕ} {a b c d : planeRectangle w h}
    (p : (rectangleGraph (planeRectangle w h)).Walk a b)
    (q : (rectangleGraph (planeRectangle w h)).Walk c d)
    (ha : a ∈ rectangleLeft (planeRectangle w h))
    (hb : b ∈ rectangleRight (planeRectangle w h))
    (hc : (c : Site 2) 1 = 0) (hd : (d : Site 2) 1 = h) :
    ∃ z : Site 2, z ∈ p.support.map (Subtype.val) ∧ z ∈ q.support.map (Subtype.val) := by
  obtain ⟨c', d', q', hc', hd', hq'⟩ := nnWalkToStar q
  obtain ⟨z, t, htp, htz, hzq⟩ := rectangle_nn_star_intersect (c := c') (d := d') p q' ha hb
    (by rw [hc']; exact hc) (by rw [hd']; exact hd)
  obtain ⟨y, hy, hzy⟩ := hq' z hzq
  refine ⟨(z : Site 2), ?_, ?_⟩
  · exact (List.mem_map (f := (Subtype.val : planeRectangle w h → Site 2))
      (l := p.support) (b := (z : Site 2))).mpr ⟨t, htp, htz.symm⟩
  · exact (List.mem_map (f := (Subtype.val : planeRectangle w h → Site 2))
      (l := q.support) (b := (z : Site 2))).mpr ⟨y, hy, hzy.symm⟩

end Sandpile