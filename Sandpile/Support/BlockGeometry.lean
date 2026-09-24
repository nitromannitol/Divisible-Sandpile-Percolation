/-
Deterministic block geometry for the dimension-four critical level-set
percolation theorem (`sandpile.tex:3979-4002`).  A coarse site `z` of the
lattice `(2r)·ℤ²` is *good* for a planar field `F` at level `ℓ` when the four
crossings of `sandpile.tex:3979-3986` hold in the four rectangles anchored at
`2r·z`: the left-right and top-bottom crossings of the side-`2r` square, the
left-right crossing of the twice-as-wide rectangle, and the top-bottom
crossing of the twice-as-tall rectangle.  The half-shifted overlap of the
wide and tall rectangles with the neighbouring squares is what makes
adjacent good coarse sites belong to one component; the paper records the
deterministic implication at `sandpile.tex:3979-3986` ("if a planar set has
all these crossings ... for every `z` in an infinite nearest-neighbor
subset, then it has an unbounded connected component").
-/
import Sandpile.Support.RectangleTranspose
import Sandpile.Support.RectangleIntersection
import Sandpile.Support.StarCrossings

open scoped NNReal
noncomputable section
namespace Sandpile

/-- An inclusion of a narrower lattice rectangle into a wider one with the
same height, as a graph homomorphism: `planeRectangle w h ↪ planeRectangle W h`
for `w ≤ W`. -/
def rectangleIncl {w W h : ℕ} (hle : w ≤ W) :
    rectangleGraph (planeRectangle w h) →g rectangleGraph (planeRectangle W h) where
  toFun z := ⟨z, by
      rw [mem_planeRectangle]
      have hz := (mem_planeRectangle w h (z : Site 2)).mp z.property
      exact ⟨hz.1, hz.2.1.trans (by exact_mod_cast hle), hz.2.2⟩⟩
  map_rel' hab := by
    exact hab

/-- An inclusion of a shorter lattice rectangle into a taller one with the
same width, as a graph homomorphism: `planeRectangle w h ↪ planeRectangle w H`
for `h ≤ H`. -/
def rectangleInclVert {w h H : ℕ} (hle : h ≤ H) :
    rectangleGraph (planeRectangle w h) →g rectangleGraph (planeRectangle w H) where
  toFun z := ⟨z, by
      rw [mem_planeRectangle]
      have hz := (mem_planeRectangle w h (z : Site 2)).mp z.property
      exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans (by exact_mod_cast hle)⟩⟩
  map_rel' hab := by
    exact hab

/-- An nearest-neighbour walk inside a lattice rectangle, viewed as a walk of
the induced star graph on the same rectangle: every nearest-neighbour step is
a star step. -/
theorem nnWalkToStar {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b) :
    ∃ (c' d' : {x : Site 2 // x ∈ ((Q : Set (Site 2)) : Set (Site 2))}),
      ∃ q : ((starLatticeGraph 2).induce ((Q : Set (Site 2)))).Walk c' d',
      (c' : Site 2) = (a : Site 2) ∧ (d' : Site 2) = (b : Site 2) ∧
      ∀ z : {x : Site 2 // x ∈ ((Q : Set (Site 2)) : Set (Site 2))},
        z ∈ q.support → ∃ y ∈ p.support, (z : Site 2) = (y : Site 2) := by
  induction p with
  | @nil u =>
    refine ⟨u, u, .nil, rfl, rfl, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    exact ⟨u, by rw [SimpleGraph.Walk.support_nil]; exact List.mem_singleton_self _, by rw [hz]⟩
  | @cons u v w hab p ih =>
    obtain ⟨c', d', q', hc', hd', hq'⟩ := ih
    have hc'' : c' = ⟨(v : Site 2), v.property⟩ := Subtype.ext hc'
    subst hc''
    refine ⟨u, d', .cons (by
      have hadj : (lattice 2).Adj (u : Site 2) (v : Site 2) := hab
      exact lattice_le_starLatticeGraph 2 hadj) q', rfl, hd', ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact ⟨u, by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_self, by rw [hz]⟩
    · obtain ⟨y, hy, hzy⟩ := hq' z hz
      exact ⟨y, by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ hy, hzy⟩

/-- A level below the crossing value is witnessed by a left-right
nearest-neighbour walk of the rectangle whose every site has field value at
least that level. -/
lemma exists_lr_walk_of_le_crossingValue {w h : ℕ} (F : planeRectangle w h → ℝ)
    {ℓ : ℝ} (hℓ : ℓ ≤ crossingValue (planeRectangle w h) F) :
    ∃ (a b : planeRectangle w h) (p : (rectangleGraph (planeRectangle w h)).Walk a b),
      a ∈ rectangleLeft (planeRectangle w h) ∧ b ∈ rectangleRight (planeRectangle w h) ∧
      ∀ z ∈ p.support, ℓ ≤ F z := by
  obtain ⟨a, b, p, hp, ha, hb, hval⟩ :=
    (crossingValue_spec (isLatticeRectangle_planeRectangle w h) (planeRectangle_nonempty w h) F).2
  have hle : ℓ ≤ walkBottleneck p F := hval ▸ hℓ
  exact ⟨a, b, p, ha, hb, fun z hz => (le_walkBottleneck_iff p F ℓ).mp hle z hz⟩

/-- Translation of a lattice rectangle by a nonnegative offset vector, as a
graph homomorphism into the enlarged rectangle. -/
def rectTranslateHom (w h a b : ℕ) :
    rectangleGraph (planeRectangle w h) →g
    rectangleGraph (planeRectangle (w + a) (h + b)) where
  toFun z := ⟨(z : Site 2) + ![(a : ℤ), (b : ℤ)], by
    have hz := (mem_planeRectangle w h (z : Site 2)).mp z.property
    rw [mem_planeRectangle]
    constructor
    · simp
      have := hz.1
      omega
    constructor
    · simp
      have := hz.2.1
      omega
    · simp
      have := hz.2.2
      omega⟩
  map_rel' hab := by
    exact lattice_adj_translate _ hab
