import Sandpile.Support.DualFlux
import Sandpile.Support.BoundaryGraph
import Sandpile.Support.GridCorners

/-!
# Star connectivity through bad sites bridged by a coloring's changing edges

Transports the abstract mod-two flux/connectivity duality of `DualFlux` and `BoundaryGraph` onto
the primal grid. `gridDualMap` sends each abstract dual vertex (a grid cell, or one of the two
poles) to a representative element of `Bool ⊕ K`, using a corner of that cell lying in `K` when
one exists (`gridFaceRepresentative`). The four `gridDualMap_*` lemmas show that the two abstract
endpoints of every primal edge map to `gridBoundaryGraph K`-reachable points whenever `K`
contains a corner incident to that edge. The main theorem
`grid_star_connection_of_mixed_edges` concludes: given a `{0, 1}`-coloring `C` of the primal grid
vertices that is `1` on the left column `i = 0` and `0` on the right column `i = Fin.last m`, if
`K` contains an endpoint of every primal edge across which `C` changes value, then `K` contains a
star-connected chain running from the bottom column `j = 0` to the top column `j = Fin.last n`.
-/

noncomputable section
namespace Sandpile

/-- `gridBoundarySets K` selects the two boundary subsets of `K` used to attach poles: `false`
picks out elements of `K` on the bottom column `j = 0`, and `true` those on the top column
`j = Fin.last n`. -/
def gridBoundarySets {m n : ℕ} (K : Set (primalGrid m n)) : Bool → Set K
  | false => {p | (p : primalGrid m n).2 = 0}
  | true => {p | (p : primalGrid m n).2 = Fin.last n}

/-- The graph on `K` given by `gridBadGraph K`, with two extra pole vertices attached to its
bottom and top boundary sets via `boundaryGraph`. -/
def gridBoundaryGraph {m n : ℕ} (K : Set (primalGrid m n)) : SimpleGraph (Bool ⊕ K) :=
  boundaryGraph (gridBadGraph K) (gridBoundarySets K)

/-- The inclusion of `gridBadGraph K` into `gridBoundaryGraph K` as the `Sum.inr` summand: a
graph homomorphism because `boundaryGraph` preserves every adjacency of the original graph. -/
def gridBadBoundaryHom {m n : ℕ} (K : Set (primalGrid m n)) :
    gridBadGraph K →g gridBoundaryGraph K :=
  ⟨Sum.inr, fun h => h⟩

/-- A representative of the cell `c` inside `Bool ⊕ K`: a corner of `c` lying in `K` if one
exists, or else the bottom pole `.inl false`. -/
def gridFaceRepresentative {m n : ℕ} (K : Set (primalGrid m n)) (c : Fin m × Fin n) :
    Bool ⊕ K := by
  classical
  exact if h : ∃ p : K, IsGridCorner c p then .inr h.choose else .inl false

/-- If `p ∈ K` is a corner of the cell `c`, then `gridFaceRepresentative K c` is reachable from
`.inr p` in `gridBoundaryGraph K`, via `gridBadGraph_corners_reachable` applied to `p` and the
corner witness chosen by `gridFaceRepresentative`. -/
lemma gridFaceRepresentative_reachable {m n : ℕ} (K : Set (primalGrid m n))
    (c : Fin m × Fin n) (p : K) (hp : IsGridCorner c p) :
    (gridBoundaryGraph K).Reachable (gridFaceRepresentative K c) (.inr p) := by
  classical
  have he : ∃ q : K, IsGridCorner c q := ⟨p, hp⟩
  simp only [gridFaceRepresentative, dif_pos he]
  exact (gridBadGraph_corners_reachable K he.choose p he.choose_spec hp).map (gridBadBoundaryHom K)

/-- Transports each abstract dual vertex (a grid cell, or one of `DualFlux`'s two poles) into
`Bool ⊕ K`, sending a cell to its `gridFaceRepresentative` and leaving the poles fixed. -/
def gridDualMap {m n : ℕ} (K : Set (primalGrid m n)) : dualVertex m n → Bool ⊕ K
  | .inl b => .inl b
  | .inr c => gridFaceRepresentative K c

/-- For a horizontal dual edge `.inl (i, j)`, if one of its two primal endpoints
`(i.castSucc, j)` or `(i.succ, j)` lies in `K` as `p`, then `gridDualMap K` sends the edge's
abstract source to a point `gridBoundaryGraph K`-reachable from `.inr p`. -/
lemma gridDualMap_horizontal_src {m n : ℕ} (K : Set (primalGrid m n))
    (i : Fin m) (j : Fin (n + 1)) (p : K)
    (hp : (p : primalGrid m n) = (i.castSucc, j) ∨ (p : primalGrid m n) = (i.succ, j)) :
    (gridBoundaryGraph K).Reachable (gridDualMap K (dualSrc (.inl (i, j)))) (.inr p) := by
  cases j using Fin.cases with
  | zero =>
    apply SimpleGraph.Adj.reachable
    change (p : primalGrid m n).2 = 0
    rcases hp with hp | hp <;> exact congrArg Prod.snd hp
  | succ j =>
    change (gridBoundaryGraph K).Reachable (gridFaceRepresentative K (i, j)) (.inr p)
    apply gridFaceRepresentative_reachable
    rcases hp with hp | hp
    · rw [hp]
      exact isGridCorner_cast_succ i j
    · rw [hp]
      exact isGridCorner_succ_succ i j

/-- For a horizontal dual edge `.inl (i, j)`, if one of its two primal endpoints
`(i.castSucc, j)` or `(i.succ, j)` lies in `K` as `p`, then `gridDualMap K` sends the edge's
abstract destination to a point `gridBoundaryGraph K`-reachable from `.inr p`. -/
lemma gridDualMap_horizontal_dst {m n : ℕ} (K : Set (primalGrid m n))
    (i : Fin m) (j : Fin (n + 1)) (p : K)
    (hp : (p : primalGrid m n) = (i.castSucc, j) ∨ (p : primalGrid m n) = (i.succ, j)) :
    (gridBoundaryGraph K).Reachable (gridDualMap K (dualDst (.inl (i, j)))) (.inr p) := by
  cases j using Fin.lastCases with
  | last =>
    simp only [dualDst, Fin.snoc_last, gridDualMap]
    apply SimpleGraph.Adj.reachable
    change (p : primalGrid m n).2 = Fin.last n
    rcases hp with hp | hp <;> exact congrArg Prod.snd hp
  | cast i' =>
    simp only [dualDst, Fin.snoc_castSucc, gridDualMap]
    apply gridFaceRepresentative_reachable
    rcases hp with hp | hp
    · rw [hp]
      exact isGridCorner_cast_cast i i'
    · rw [hp]
      exact isGridCorner_succ_cast i i'

/-- For a vertical dual edge `.inr (i, j)` with `i ≠ 0`, if one of its two primal endpoints
`(i, j.castSucc)` or `(i, j.succ)` lies in `K` as `p`, then `gridDualMap K` sends the edge's
abstract source to a point `gridBoundaryGraph K`-reachable from `.inr p`. -/
lemma gridDualMap_vertical_src {m n : ℕ} (K : Set (primalGrid m n))
    (i : Fin (m + 1)) (j : Fin n) (hi : i ≠ 0) (p : K)
    (hp : (p : primalGrid m n) = (i, j.castSucc) ∨ (p : primalGrid m n) = (i, j.succ)) :
    (gridBoundaryGraph K).Reachable (gridDualMap K (dualSrc (.inr (i, j)))) (.inr p) := by
  cases i using Fin.cases with
  | zero => exact (hi rfl).elim
  | succ i =>
    change (gridBoundaryGraph K).Reachable (gridFaceRepresentative K (i, j)) (.inr p)
    apply gridFaceRepresentative_reachable
    rcases hp with hp | hp
    · rw [hp]
      exact isGridCorner_succ_cast i j
    · rw [hp]
      exact isGridCorner_succ_succ i j

/-- For a vertical dual edge `.inr (i, j)` with `i ≠ Fin.last m`, if one of its two primal
endpoints `(i, j.castSucc)` or `(i, j.succ)` lies in `K` as `p`, then `gridDualMap K` sends the
edge's abstract destination to a point `gridBoundaryGraph K`-reachable from `.inr p`. -/
lemma gridDualMap_vertical_dst {m n : ℕ} (K : Set (primalGrid m n))
    (i : Fin (m + 1)) (j : Fin n) (hi : i ≠ Fin.last m) (p : K)
    (hp : (p : primalGrid m n) = (i, j.castSucc) ∨ (p : primalGrid m n) = (i, j.succ)) :
    (gridBoundaryGraph K).Reachable (gridDualMap K (dualDst (.inr (i, j)))) (.inr p) := by
  cases i using Fin.lastCases with
  | last => exact (hi rfl).elim
  | cast i =>
    simp only [dualDst, Fin.snoc_castSucc, gridDualMap]
    apply gridFaceRepresentative_reachable
    rcases hp with hp | hp
    · rw [hp]
      exact isGridCorner_cast_cast i j
    · rw [hp]
      exact isGridCorner_cast_succ i j

/-- **The main duality theorem.** If a `{0, 1}`-coloring `C` of the primal grid is `1` on the
left column `i = 0` and `0` on the right column `i = Fin.last m`, and `K` contains an endpoint of
every horizontal (`hH`) or vertical (`hV`) primal edge across which `C` changes value, then `K`
contains a bottom vertex `a` (with `a.2 = 0`), a top vertex `b` (with `b.2 = Fin.last n`), and a
star-connected path from `a` to `b` in `gridBadGraph K`. The proof transports the abstract
bottom-to-top flux connectivity of `dual_flux_identity` along `gridDualMap` and reads off the
primal connection via `boundaryGraph_reachable_iff`. -/
lemma grid_star_connection_of_mixed_edges {m n : ℕ}
    (C : Fin (m + 1) → Fin (n + 1) → ZMod 2)
    (hleft : ∀ j, C 0 j = 1) (hright : ∀ j, C (Fin.last m) j = 0)
    (K : Set (primalGrid m n))
    (hH : ∀ i : Fin m, ∀ j : Fin (n + 1), C i.castSucc j + C i.succ j ≠ 0 →
      (i.castSucc, j) ∈ K ∨ (i.succ, j) ∈ K)
    (hV : ∀ i : Fin (m + 1), ∀ j : Fin n, C i j.castSucc + C i j.succ ≠ 0 →
      (i, j.castSucc) ∈ K ∨ (i, j.succ) ∈ K) :
    ∃ a b : K, (a : primalGrid m n).2 = 0 ∧ (b : primalGrid m n).2 = Fin.last n ∧
      (gridBadGraph K).Reachable a b := by
  have he : ∀ e : dualEdge m n, dualWeight C e ≠ 0 →
      (gridBoundaryGraph K).Reachable (gridDualMap K (dualSrc e)) (gridDualMap K (dualDst e)) := by
    intro e he
    rcases e with ⟨i, j⟩ | ⟨i, j⟩
    · have connect (p : K) (hp : (p : primalGrid m n) = (i.castSucc, j) ∨
          (p : primalGrid m n) = (i.succ, j)) :
          (gridBoundaryGraph K).Reachable (gridDualMap K (dualSrc (.inl (i, j))))
            (gridDualMap K (dualDst (.inl (i, j)))) :=
        (gridDualMap_horizontal_src K i j p hp).trans (gridDualMap_horizontal_dst K i j p hp).symm
      rcases hH i j he with hp | hp
      · exact connect ⟨(i.castSucc, j), hp⟩ (Or.inl rfl)
      · exact connect ⟨(i.succ, j), hp⟩ (Or.inr rfl)
    · have hi0 : i ≠ 0 := by
        intro hi
        apply he
        simp only [dualWeight, hi, hleft, CharTwo.add_self_eq_zero]
      have hilast : i ≠ Fin.last m := by
        intro hi
        apply he
        simp only [dualWeight, hi, hright, CharTwo.add_self_eq_zero]
      have connect (p : K) (hp : (p : primalGrid m n) = (i, j.castSucc) ∨
          (p : primalGrid m n) = (i, j.succ)) :
          (gridBoundaryGraph K).Reachable (gridDualMap K (dualSrc (.inr (i, j))))
            (gridDualMap K (dualDst (.inr (i, j)))) :=
        (gridDualMap_vertical_src K i j hi0 p hp).trans
          (gridDualMap_vertical_dst K i j hilast p hp).symm
      rcases hV i j he with hp | hp
      · exact connect ⟨(i, j.castSucc), hp⟩ (Or.inl rfl)
      · exact connect ⟨(i, j.succ), hp⟩ (Or.inr rfl)
  have hc := reachable_of_mod_two_flux (gridBoundaryGraph K)
    (fun e => gridDualMap K (dualSrc e)) (fun e => gridDualMap K (dualDst e)) (dualWeight C)
    (.inl false) (.inl true) he
    (fun f => dual_flux_identity C hleft hright (fun v => f (gridDualMap K v)))
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (boundaryGraph_reachable_iff (gridBadGraph K) (gridBoundarySets K)).mp hc
  exact ⟨a, b, ha, hb, hab⟩

end Sandpile
