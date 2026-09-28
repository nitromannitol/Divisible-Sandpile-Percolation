import Sandpile.Support.GridDuality
import Sandpile.Support.StarNN

/-!
# No open left-right crossing forces a closed star crossing

Discrete percolation duality on a finite `primalGrid m n`. `gridLeftColor O` is the `ZMod 2`
indicator of `gridLeftReachable O`, connection to the left edge (`.1 = 0`) through open sites
`O` along the nearest-neighbor graph `gridOpenGraph O`; it can only change across a primal
edge with a closed endpoint (`grid_closed_endpoint_of_color_change`, via
`gridLeftColor_eq_of_open_adj`). Feeding this coloring, which is `1` on the whole left edge
and `0` on the whole right edge whenever there is no open left-right crossing, into
`grid_star_connection_of_mixed_edges` from `GridDuality` yields the main result
`grid_star_crossing_of_no_open_lr`: if every left-edge site is open but no open path in `O`
reaches the right edge (`.1 = Fin.last m`), then the closed complement `Oᶜ` contains a
star-connected path (`gridBadGraph`, diagonal adjacency via `starLatticeGraph`) between the
two perpendicular edges `.2 = 0` and `.2 = Fin.last n`.
-/

noncomputable section
namespace Sandpile

/-- The nearest-neighbor graph on the open sites `O`, obtained by restricting the ambient
`lattice 2` graph (via `gridSite`) to `O`. -/
def gridOpenGraph {m n : ℕ} (O : Set (primalGrid m n)) : SimpleGraph O :=
  (lattice 2).comap (fun p : O => gridSite (p : primalGrid m n))

/-- `p` is reachable from the left edge of the grid (a site with first coordinate `0`) by a
path through open sites of `O`, using `gridOpenGraph O`. -/
def gridLeftReachable {m n : ℕ} (O : Set (primalGrid m n)) (p : primalGrid m n) : Prop :=
  ∃ a b : O, (a : primalGrid m n).1 = 0 ∧ (b : primalGrid m n) = p ∧
    (gridOpenGraph O).Reachable a b

/-- The `ZMod 2` indicator of `gridLeftReachable O p`: `1` if `p` is connected to the left
edge through open sites of `O`, and `0` otherwise. -/
def gridLeftColor {m n : ℕ} (O : Set (primalGrid m n)) (p : primalGrid m n) : ZMod 2 := by
  classical
  exact if gridLeftReachable O p then 1 else 0

/-- Every open site on the left edge, `(0, j) ∈ O`, is left-reachable via the trivial
one-point path. -/
lemma gridLeftReachable_seed {m n : ℕ} (O : Set (primalGrid m n))
    (j : Fin (n + 1)) (hj : (0, j) ∈ O) : gridLeftReachable O (0, j) := by
  let p : O := ⟨(0, j), hj⟩
  exact ⟨p, p, rfl, rfl, SimpleGraph.Reachable.refl p⟩

/-- Left-reachability propagates across a single primal-grid edge: if `p` is left-reachable,
`q` is open, and `p`, `q` are adjacent in `lattice 2`, then `q` is left-reachable too. -/
lemma gridLeftReachable_step {m n : ℕ} (O : Set (primalGrid m n))
    {p q : primalGrid m n} (hp : gridLeftReachable O p) (hq : q ∈ O)
    (hpq : (lattice 2).Adj (gridSite p) (gridSite q)) : gridLeftReachable O q := by
  obtain ⟨a, b, ha, hb, hab⟩ := hp
  let c : O := ⟨q, hq⟩
  refine ⟨a, c, ha, rfl, hab.trans ?_⟩
  apply SimpleGraph.Adj.reachable
  change (lattice 2).Adj (gridSite (b : primalGrid m n)) (gridSite q)
  rw [hb]
  exact hpq

/-- Adjacent open sites share the same `gridLeftColor`, since `gridLeftReachable_step`
transfers left-reachability both ways across an open edge. -/
lemma gridLeftColor_eq_of_open_adj {m n : ℕ} (O : Set (primalGrid m n))
    {p q : primalGrid m n} (hp : p ∈ O) (hq : q ∈ O)
    (hpq : (lattice 2).Adj (gridSite p) (gridSite q)) : gridLeftColor O p = gridLeftColor O q := by
  classical
  have hh : gridLeftReachable O p ↔ gridLeftReachable O q :=
    ⟨fun h => gridLeftReachable_step O h hq hpq, fun h => gridLeftReachable_step O h hp hpq.symm⟩
  simp only [gridLeftColor, hh]

/-- Contrapositive of `gridLeftColor_eq_of_open_adj`: if a primal-grid edge's endpoints have
different `gridLeftColor`s (their sum is nonzero in `ZMod 2`), at least one endpoint lies in
the closed complement `Oᶜ`. -/
lemma grid_closed_endpoint_of_color_change {m n : ℕ} (O : Set (primalGrid m n))
    {p q : primalGrid m n} (hpq : (lattice 2).Adj (gridSite p) (gridSite q))
    (hc : gridLeftColor O p + gridLeftColor O q ≠ 0) : p ∈ Oᶜ ∨ q ∈ Oᶜ := by
  by_cases hp : p ∈ O
  · by_cases hq : q ∈ O
    · apply False.elim
      apply hc
      rw [gridLeftColor_eq_of_open_adj O hp hq hpq]
      exact CharTwo.add_self_eq_zero _
    · exact Or.inr hq
  · exact Or.inl hp

/-- Horizontally adjacent primal-grid sites `(i.castSucc, j)` and `(i.succ, j)` are adjacent
in `lattice 2` under `gridSite`, via `lattice_adj_of_one_coordinate` on the first
coordinate. -/
lemma grid_horizontal_adj {m n : ℕ} (i : Fin m) (j : Fin (n + 1)) :
    (lattice 2).Adj (gridSite (i.castSucc, j)) (gridSite (i.succ, j)) := by
  apply lattice_adj_of_one_coordinate (i := (0 : Fin 2))
  · intro k hk
    fin_cases k
    · exact (hk rfl).elim
    · rfl
  · simp [gridSite]

/-- Vertically adjacent primal-grid sites `(i, j.castSucc)` and `(i, j.succ)` are adjacent
in `lattice 2` under `gridSite`, via `lattice_adj_of_one_coordinate` on the second
coordinate. -/
lemma grid_vertical_adj {m n : ℕ} (i : Fin (m + 1)) (j : Fin n) :
    (lattice 2).Adj (gridSite (i, j.castSucc)) (gridSite (i, j.succ)) := by
  apply lattice_adj_of_one_coordinate (i := (1 : Fin 2))
  · intro k hk
    fin_cases k
    · rfl
    · exact (hk rfl).elim
  · simp [gridSite]

/-- Grid duality: if every left-edge site is open and no open path in `O` reaches the right
edge (`.1 = Fin.last m`), the closed complement `Oᶜ` contains a star-connected path
(`gridBadGraph`) between the two perpendicular edges `.2 = 0` and `.2 = Fin.last n`. Proved
by feeding the `gridLeftColor` coloring, which is `1` on the left edge and `0` on the right
edge under these hypotheses, into `grid_star_connection_of_mixed_edges`. -/
lemma grid_star_crossing_of_no_open_lr {m n : ℕ} (O : Set (primalGrid m n))
    (hleft : ∀ j : Fin (n + 1), (0, j) ∈ O)
    (hno : ¬∃ a b : O, (a : primalGrid m n).1 = 0 ∧ (b : primalGrid m n).1 = Fin.last m ∧
      (gridOpenGraph O).Reachable a b) :
    ∃ a b : (Oᶜ : Set (primalGrid m n)),
      (a : primalGrid m n).2 = 0 ∧ (b : primalGrid m n).2 = Fin.last n ∧
      (gridBadGraph Oᶜ).Reachable a b := by
  classical
  have hCleft (j : Fin (n + 1)) : gridLeftColor O (0, j) = 1 := by
    simp only [gridLeftColor, if_pos (gridLeftReachable_seed O j (hleft j))]
  have hCright (j : Fin (n + 1)) : gridLeftColor O (Fin.last m, j) = 0 := by
    have hn : ¬gridLeftReachable O (Fin.last m, j) := by
      rintro ⟨a, b, ha, hb, hab⟩
      exact hno ⟨a, b, ha, congrArg Prod.fst hb, hab⟩
    simp only [gridLeftColor, if_neg hn]
  apply grid_star_connection_of_mixed_edges (fun i j => gridLeftColor O (i, j)) hCleft hCright
  · intro i j hh
    exact grid_closed_endpoint_of_color_change O (grid_horizontal_adj i j) hh
  · intro i j hh
    exact grid_closed_endpoint_of_color_change O (grid_vertical_adj i j) hh

end Sandpile
