import Sandpile.External.RSW.FirstRectangleExit
import Sandpile.External.RSW.ArcIntersection

/-!
# First exit between two vertical paths

A path entering a rectangle between two vertical paths either reaches the central part
of the opposite side or meets one of the vertical paths before leaving the rectangle.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A first exit from between two vertical paths either reaches the central top interval
or intersects one of the paths. -/
theorem central_corridor_first_exit {L R B T lc ld rc rd : ℤ}
    (hL : L < lc) (hR : rd < R) (hBT : B < T)
    (hleft : lc ≤ ld) (hbetween : ld ≤ rc) (hright : rc ≤ rd)
    {a₁ b₁ a₂ b₂ u v : Site 2}
    (p₁ : (LatticeModels.zdGraph 2).Walk a₁ b₁)
    (p₂ : (LatticeModels.zdGraph 2).Walk a₂ b₂)
    (p : (LatticeModels.zdGraph 2).Walk u v)
    (hp₁ : ∀ z ∈ p₁.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hp₂ : ∀ z ∈ p₂.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha₁ : a₁ 1 = T ∧ lc ≤ a₁ 0 ∧ a₁ 0 ≤ ld)
    (hb₁ : b₁ 1 = B ∧ lc ≤ b₁ 0 ∧ b₁ 0 ≤ ld)
    (ha₂ : a₂ 1 = T ∧ rc ≤ a₂ 0 ∧ a₂ 0 ≤ rd)
    (hb₂ : b₂ 1 = B ∧ rc ≤ b₂ 0 ∧ b₂ 0 ≤ rd)
    (hu : u 1 = B ∧ ld ≤ u 0 ∧ u 0 ≤ rc) (hv : T ≤ v 1)
    (hpBottom : ∀ z ∈ p.support, B ≤ z 1) :
    (∃ z ∈ p₁.support, z ∈ p.support) ∨ (∃ z ∈ p₂.support, z ∈ p.support) ∨
      ∃ (c : Site 2) (q : (LatticeModels.zdGraph 2).Walk u c),
        c 1 = T ∧ lc ≤ c 0 ∧ c 0 ≤ rd ∧
        (∀ z ∈ q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T) ∧
        (∀ z ∈ q.support, z ∈ p.support) ∧ (∀ e ∈ q.edges, e ∈ p.edges) := by
  obtain ⟨c, q, hc, hqbox, hqs, hqe⟩ := exists_first_rectangle_exit p
    (by omega : L ≤ u 0) (by omega : u 0 ≤ R) (by omega : u 1 ≤ T) hv hpBottom
  have hqrev : ∀ z ∈ q.reverse.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T := by
    intro z hz
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    exact hqbox z hz
  have hhitLeft (hcL : c 0 = L ∨ (c 0 ≤ lc ∧ (c 1 = B ∨ c 1 = T))) :
      ∃ z ∈ p₁.support, z ∈ p.support := by
    obtain ⟨z, h₁, hq⟩ := alternating_boundary_paths_intersect hL (by omega : ld < R) hBT
      p₁ q.reverse hp₁ hqrev ha₁ hb₁ hcL (Or.inr ⟨hu.2.1, Or.inl hu.1⟩)
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hq
    exact ⟨z, h₁, hqs z hq⟩
  have hhitRight (hcR : c 0 = R ∨ (rd ≤ c 0 ∧ (c 1 = B ∨ c 1 = T))) :
      ∃ z ∈ p₂.support, z ∈ p.support := by
    obtain ⟨z, h₂, hq⟩ := alternating_boundary_paths_intersect (by omega : L < rc) hR hBT
      p₂ q hp₂ hqbox ha₂ hb₂ (Or.inr ⟨hu.2.2, Or.inl hu.1⟩) hcR
    exact ⟨z, h₂, hqs z hq⟩
  rcases hc with hcL | hcR | hcT
  · exact Or.inl (hhitLeft (Or.inl hcL))
  · exact Or.inr (Or.inl (hhitRight (Or.inl hcR)))
  · by_cases hcl : c 0 < lc
    · exact Or.inl (hhitLeft (Or.inr ⟨by omega, Or.inr hcT⟩))
    · by_cases hcr : rd < c 0
      · exact Or.inr (Or.inl (hhitRight (Or.inr ⟨by omega, Or.inr hcT⟩)))
      · exact Or.inr (Or.inr ⟨c, q, hcT, by omega, by omega, hqbox, hqs, hqe⟩)

end Sandpile.External.RSW
