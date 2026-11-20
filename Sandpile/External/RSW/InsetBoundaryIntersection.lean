import Sandpile.External.RSW.ArcIntersection

/-!
# Boundary intersection for an inset path

A vertical path whose endpoints lie one step inside a rectangle meets a path
joining the opposite boundary arcs, unless that path meets one of the two
one-edge endpoint extensions.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- Alternating boundary paths intersect after extending an inset vertical path. -/
theorem inset_vertical_walk_intersects_boundary_walk {L R B T c d : ℤ}
    (hLc : L < c) (hdR : d < R) (hBT : B < T)
    {a b u v : Site 2} (p : (LatticeModels.zdGraph 2).Walk a b)
    (q : (LatticeModels.zdGraph 2).Walk u v)
    (hp : ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B + 1 ≤ z 1 ∧ z 1 ≤ T - 1)
    (hq : ∀ z ∈ q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 1 = T - 1 ∧ c ≤ a 0 ∧ a 0 ≤ d)
    (hb : b 1 = B + 1 ∧ c ≤ b 0 ∧ b 0 ≤ d)
    (hu : u 0 = L ∨ (u 0 ≤ c ∧ (u 1 = B ∨ u 1 = T)))
    (hv : v 0 = R ∨ (d ≤ v 0 ∧ (v 1 = B ∨ v 1 = T))) :
    (∃ z ∈ p.support, z ∈ q.support) ∨
      a + Pi.single 1 1 ∈ q.support ∨ b - Pi.single 1 1 ∈ q.support := by
  let top : Site 2 := a + Pi.single 1 1
  let bot : Site 2 := b - Pi.single 1 1
  have htop0 : top 0 = a 0 := by simp [top]
  have htop1 : top 1 = T := by simp [top, ha.1]
  have hbot0 : bot 0 = b 0 := by simp [bot]
  have hbot1 : bot 1 = B := by simp [bot, hb.1]
  have htop_eq : top - Pi.single 1 1 = a := by simp [top]
  have htop_adj : (LatticeModels.zdGraph 2).Adj top a := by
    simpa only [htop_eq] using adj_sub_single_one top
  have hbot_adj : (LatticeModels.zdGraph 2).Adj b bot := adj_sub_single_one b
  let w := htop_adj.toWalk.append (p.append hbot_adj.toWalk)
  have hw : ∀ z ∈ w.support, z = top ∨ z ∈ p.support ∨ z = bot := by
    intro z hz
    change z ∈ (htop_adj.toWalk.append (p.append hbot_adj.toWalk)).support at hz
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Adj.toWalk,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    rcases hz with (rfl | rfl) | hz | (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl p.start_mem_support)
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inl p.end_mem_support)
    · exact Or.inr (Or.inr rfl)
  have hwbox : ∀ z ∈ w.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T := by
    intro z hz
    rcases hw z hz with rfl | hz | rfl
    · rw [htop0, htop1]; have h := hp a p.start_mem_support; omega
    · have h := hp z hz; omega
    · rw [hbot0, hbot1]; have h := hp b p.end_mem_support; omega
  obtain ⟨z, hzw, hzq⟩ := alternating_boundary_paths_intersect hLc hdR hBT w q hwbox hq
    ⟨htop1, by rw [htop0]; exact ha.2.1, by rw [htop0]; exact ha.2.2⟩
    ⟨hbot1, by rw [hbot0]; exact hb.2.1, by rw [hbot0]; exact hb.2.2⟩ hu hv
  rcases hw z hzw with rfl | hz | rfl
  · exact Or.inr (Or.inl hzq)
  · exact Or.inl ⟨z, hz, hzq⟩
  · exact Or.inr (Or.inr hzq)

end Sandpile.External.RSW
