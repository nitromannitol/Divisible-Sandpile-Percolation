import Sandpile.External.RSW.SiteBondCrossing
import LatticeProb.Vendor.FormalMathPercolation.Literature.PlanarDuality

/-!
# Discrete bond crossing duality

The dual rectangle extends half a lattice spacing beyond the horizontal sides of the
primal rectangle. Its vertices are represented by the lower-left corners of dual faces.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- The two presentations of nearest-neighbor adjacency on the integer lattice agree. -/
theorem lattice_eq_zdGraph (d : ℕ) : lattice d = LatticeModels.zdGraph d := by
  ext x y
  rw [LatticeModels.zdGraph_adj_iff]
  rfl

/-- The open lattice edges of a Boolean bond configuration. -/
def openPlaneBonds (ω : Sym2 (Site 2) → Bool) : Set (Sym2 (Site 2)) :=
  {e | e ∈ (lattice 2).edgeSet ∧ ω e = true}

/-- The edge-set configuration contains only lattice edges. -/
theorem openPlaneBonds_subset (ω : Sym2 (Site 2) → Bool) :
    openPlaneBonds ω ⊆ (LatticeModels.zdGraph 2).edgeSet := by
  rw [← lattice_eq_zdGraph]
  exact fun _ h => h.1

/-- A rectangle walk is open exactly when all edges of its ambient walk are open. -/
theorem isBondOpenWalk_iff_edges {Q : Finset (Site 2)} (ω : Sym2 (Site 2) → Bool)
    {a b : Q} (p : (rectangleGraph Q).Walk a b) :
    IsBondOpenWalk ω p ↔
      ∀ e ∈ (p.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom).edges,
        ω e = true := by
  induction p with
  | nil =>
    change True ↔ ∀ e ∈ ([] : List (Sym2 (Site 2))), ω e = true
    simp only [List.not_mem_nil, false_implies, implies_true]
  | @cons a b c hab p ih =>
    change (ω s((a : Site 2), (b : Site 2)) = true ∧ IsBondOpenWalk ω p) ↔
      ∀ e ∈ s((a : Site 2), (b : Site 2)) ::
        (p.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom).edges, ω e = true
    simp only [List.mem_cons, forall_eq_or_imp, ← ih]

/-- The origin-based rectangle is the same rectangle used by lattice bond duality. -/
theorem planeRectangle_eq_rectangle (w h : ℕ) :
    planeRectangle w h = Percolation.Literature.rectangle w h := by
  ext z
  rw [mem_planeRectangle, Percolation.Literature.mem_rectangle_iff]

/-- The Boolean crossing event is the lattice edge-set crossing event. -/
theorem mem_bondCrossingEvent_iff_lrCrossing (w h : ℕ) (ω : Sym2 (Site 2) → Bool) :
    ω ∈ bondCrossingEvent w h ↔ openPlaneBonds ω ∈ Percolation.Literature.lrCrossing w h := by
  have hQ : planeRectangle w h = Percolation.Literature.rectangle w h :=
    planeRectangle_eq_rectangle w h
  constructor
  · rintro ⟨a, b, p, ha, hb, hp⟩
    have ha' := (mem_rectangleLeft_planeRectangle a).mp ha
    have hb' := (mem_rectangleRight_planeRectangle b).mp hb
    refine ⟨a, ?_, b, ?_, ?_⟩
    · change (a : Site 2) ∈ Percolation.Literature.leftSide w h
      simp only [Percolation.Literature.leftSide, Finset.mem_filter]
      exact ⟨hQ ▸ a.property, ha'⟩
    · change (b : Site 2) ∈ Percolation.Literature.rightSide w h
      simp only [Percolation.Literature.rightSide, Finset.mem_filter]
      exact ⟨hQ ▸ b.property, hb'⟩
    · change ((lattice 2).induce (planeRectangle w h : Set (Site 2))).Walk a b at p
      let q := p.map (SimpleGraph.Embedding.induce (planeRectangle w h : Set (Site 2))).toHom
      apply Percolation.Literature.mem_openConnIn_of_walk q
      · intro z hz
        change z ∈ (p.map (SimpleGraph.Embedding.induce (planeRectangle w h : Set (Site 2))).toHom).support at hz
        rw [SimpleGraph.Walk.support_map] at hz
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
        exact hQ ▸ v.property
      · intro e he
        have he' := (isBondOpenWalk_iff_edges ω p).mp hp e he
        exact ⟨SimpleGraph.Walk.edges_subset_edgeSet q he, he'⟩
  · intro hc
    obtain ⟨a, ha, b, hb, hc⟩ := hc
    have hsub : openPlaneBonds ω ⊆ (lattice 2).edgeSet := fun _ he => he.1
    obtain ⟨p, hpQ, hpω⟩ := Percolation.Literature.exists_walk_of_mem_openConnIn
      (G := lattice 2) hsub hc
    have hpQ' : ∀ z ∈ p.support, z ∈ (planeRectangle w h : Set (Site 2)) := by
      intro z hz
      rw [hQ]
      exact hpQ z hz
    let q := p.induce (planeRectangle w h : Set (Site 2)) hpQ'
    refine ⟨⟨a, hpQ' a p.start_mem_support⟩, ⟨b, hpQ' b p.end_mem_support⟩, q, ?_, ?_, ?_⟩
    · apply (mem_rectangleLeft_planeRectangle _).mpr
      exact (Finset.mem_filter.mp ha).2
    · apply (mem_rectangleRight_planeRectangle _).mpr
      exact (Finset.mem_filter.mp hb).2
    · apply (isBondOpenWalk_iff_edges ω q).mpr
      intro e he
      rw [SimpleGraph.Walk.map_induce] at he
      exact (hpω e he).2

/-- A primal horizontal crossing and the shifted dual vertical crossing are complementary. -/
theorem bondCrossingEvent_iff_not_dualTBCrossing (w h : ℕ)
    (ω : Sym2 (Site 2) → Bool) :
    ω ∈ bondCrossingEvent w h ↔
      openPlaneBonds ω ∉ Percolation.Literature.dualTBCrossing w h := by
  rw [mem_bondCrossingEvent_iff_lrCrossing]
  rcases Percolation.Literature.lrCrossing_xor_dualTBCrossing_holds w h
    (openPlaneBonds_subset ω) with h | h
  · exact ⟨fun _ => h.2, fun _ => h.1⟩
  · exact ⟨fun hc => (h.2 hc).elim, fun hn => (hn h.1).elim⟩

end Sandpile.External.RSW
