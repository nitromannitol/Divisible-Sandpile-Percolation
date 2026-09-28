import Sandpile.Support.StarCrossings

/-!
# Star connectivity of bad corners in a finite lattice grid

For a finite grid `primalGrid m n := Fin (m + 1) × Fin (n + 1)`, `IsGridCorner c p` records that
a vertex `p` is one of the four corners of the unit cell indexed by `c : Fin m × Fin n`. Any two
corners of the same cell are equal or adjacent in the star (king-move) lattice graph
(`gridCorners_eq_or_star_adj`), hence reachable in the induced subgraph `gridBadGraph K` on any
subset `K` of vertices containing both of them (`gridBadGraph_corners_reachable`). This upgrades
a percolating pattern of cells into a single connected component of star-adjacent grid vertices.
The four `isGridCorner_*` lemmas record that the actual corners of a unit cell satisfy
`IsGridCorner`.
-/

namespace Sandpile

/-- The vertex set of an `m × n` grid of unit cells: an `(m + 1) × (n + 1)` array of lattice
points. -/
abbrev primalGrid (m n : ℕ) := Fin (m + 1) × Fin (n + 1)

/-- Embeds a grid vertex `p : primalGrid m n` as the `Site 2` with the same integer
coordinates. -/
def gridSite {m n : ℕ} (p : primalGrid m n) : Site 2 := ![(p.1.val : ℤ), (p.2.val : ℤ)]

/-- `gridSite` is injective: distinct grid vertices map to distinct sites. -/
lemma gridSite_injective {m n : ℕ} : Function.Injective (@gridSite m n) := by
  intro p q hpq
  apply Prod.ext
  · apply Fin.ext
    have hh := congr_fun hpq 0
    change (p.1.val : ℤ) = q.1.val at hh
    exact_mod_cast hh
  · apply Fin.ext
    have hh := congr_fun hpq 1
    change (p.2.val : ℤ) = q.2.val at hh
    exact_mod_cast hh

/-- `IsGridCorner c p` holds when the vertex `p` is one of the four corners of the unit cell
indexed by `c`, i.e. each coordinate of `p` lies within `1` of the corresponding coordinate of
`c`. -/
def IsGridCorner {m n : ℕ} (c : Fin m × Fin n) (p : primalGrid m n) : Prop :=
  c.1.val ≤ p.1.val ∧ p.1.val ≤ c.1.val + 1 ∧ c.2.val ≤ p.2.val ∧ p.2.val ≤ c.2.val + 1

/-- Two corners of the same cell `c` are either equal or adjacent in `starLatticeGraph 2`, since
`IsGridCorner` forces each coordinate difference to lie in `{0, 1}`. -/
lemma gridCorners_eq_or_star_adj {m n : ℕ} {c : Fin m × Fin n} {p q : primalGrid m n}
    (hp : IsGridCorner c p) (hq : IsGridCorner c q) :
    p = q ∨ (starLatticeGraph 2).Adj (gridSite p) (gridSite q) := by
  by_cases he : p = q
  · exact Or.inl he
  right
  refine ⟨fun hh => he (gridSite_injective hh), ?_⟩
  intro i
  have hcast : ∀ a b : ℕ, |(a : ℤ) - b| ≤ 1 → ((a : ℤ) - b).natAbs ≤ 1 := by
    intro a b hh
    have hh' : (((a : ℤ) - b).natAbs : ℤ) ≤ 1 := by simpa only [Int.natCast_natAbs] using hh
    exact_mod_cast hh'
  dsimp only [IsGridCorner] at hp hq
  fin_cases i
  · change ((p.1.val : ℤ) - q.1.val).natAbs ≤ 1
    apply hcast
    apply abs_le.mpr
    constructor <;> omega
  · change ((p.2.val : ℤ) - q.2.val).natAbs ≤ 1
    apply hcast
    apply abs_le.mpr
    constructor <;> omega

/-- The induced subgraph of `starLatticeGraph 2` on a set `K` of grid vertices, pulled back
along `gridSite`. -/
def gridBadGraph {m n : ℕ} (K : Set (primalGrid m n)) : SimpleGraph K :=
  (starLatticeGraph 2).comap (fun p : K => gridSite (p : primalGrid m n))

/-- Any two elements of `K` that are both corners of the same cell `c` are reachable in
`gridBadGraph K`, by `gridCorners_eq_or_star_adj`. -/
lemma gridBadGraph_corners_reachable {m n : ℕ} (K : Set (primalGrid m n))
    {c : Fin m × Fin n} (p q : K) (hp : IsGridCorner c p) (hq : IsGridCorner c q) :
    (gridBadGraph K).Reachable p q := by
  rcases gridCorners_eq_or_star_adj hp hq with he | he
  · have hh : p = q := Subtype.ext he
    rw [hh]
  · exact (show (gridBadGraph K).Adj p q from he).reachable

/-- The vertex `(i.castSucc, j.castSucc)` is a corner of the cell `(i, j)`. -/
lemma isGridCorner_cast_cast {m n : ℕ} (i : Fin m) (j : Fin n) :
    IsGridCorner (i, j) (i.castSucc, j.castSucc) := by simp [IsGridCorner]

/-- The vertex `(i.succ, j.castSucc)` is a corner of the cell `(i, j)`. -/
lemma isGridCorner_succ_cast {m n : ℕ} (i : Fin m) (j : Fin n) :
    IsGridCorner (i, j) (i.succ, j.castSucc) := by simp [IsGridCorner]

/-- The vertex `(i.castSucc, j.succ)` is a corner of the cell `(i, j)`. -/
lemma isGridCorner_cast_succ {m n : ℕ} (i : Fin m) (j : Fin n) :
    IsGridCorner (i, j) (i.castSucc, j.succ) := by simp [IsGridCorner]

/-- The vertex `(i.succ, j.succ)` is a corner of the cell `(i, j)`, the fourth and last of its
corners. -/
lemma isGridCorner_succ_succ {m n : ℕ} (i : Fin m) (j : Fin n) :
    IsGridCorner (i, j) (i.succ, j.succ) := by simp [IsGridCorner]

end Sandpile
