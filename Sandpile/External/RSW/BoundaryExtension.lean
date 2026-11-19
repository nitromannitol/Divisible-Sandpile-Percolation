import Sandpile.External.RSW.HorizontalWalk

/-!
# Extensions outside a rectangle

A walk endpoint on a left boundary arc can be joined to the left side of an enlarged
rectangle using only the endpoint and sites just outside the original rectangle.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Extend a point on the left boundary arc to the left side of the rectangle expanded
by one lattice step. -/
theorem exists_left_boundary_extension (L R B T c : ℤ) (u : Site 2)
    (hbox : L ≤ u 0 ∧ u 0 ≤ R ∧ B ≤ u 1 ∧ u 1 ≤ T)
    (hleft : u 0 = L ∨ (u 0 ≤ c ∧ (u 1 = B ∨ u 1 = T))) :
    ∃ (a : Site 2) (p : (LatticeModels.zdGraph 2).Walk a u), a 0 = L - 1 ∧
      ∀ z ∈ p.support,
        (L - 1 ≤ z 0 ∧ z 0 ≤ R + 1 ∧ B - 1 ≤ z 1 ∧ z 1 ≤ T + 1) ∧
        (z = u ∨ z 0 = L - 1 ∨
          (z 0 ≤ u 0 ∧ ((z 1 = B - 1 ∧ u 1 = B) ∨ (z 1 = T + 1 ∧ u 1 = T)))) := by
  have hBT : B ≤ T := by omega
  rcases hleft with hside | ⟨hc, hbottom | htop⟩
  · let a : Site 2 := pt (L - 1) (u 1)
    obtain ⟨p, hp⟩ := exists_horizontal_walk a u (by simp [a, pt]; omega) (by simp [a, pt])
    refine ⟨a, p, by simp [a, pt], ?_⟩
    intro z hz
    have hh := hp z hz
    have ha0 : a 0 = L - 1 := by simp [a, pt]
    have ha1 : a 1 = u 1 := by simp [a, pt]
    rw [ha0, ha1] at hh
    refine ⟨by omega, ?_⟩
    by_cases hzside : z 0 = L - 1
    · exact Or.inr (Or.inl hzside)
    · left
      apply LatticeModels.Site.eq_iff_two.mpr
      constructor <;> omega
  · let u' : Site 2 := u - Pi.single 1 1
    let a : Site 2 := pt (L - 1) (B - 1)
    have hu'0 : u' 0 = u 0 := by simp [u']
    have hu'1 : u' 1 = B - 1 := by simp [u', hbottom]
    obtain ⟨p, hp⟩ := exists_horizontal_walk a u' (by simp [a, pt, hu'0]; omega)
      (by simp [a, pt, hu'1])
    have hadj : (LatticeModels.zdGraph 2).Adj u' u := (adj_sub_single_one u).symm
    refine ⟨a, p.append hadj.toWalk, by simp [a, pt], ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hh := hp z hz
      have ha0 : a 0 = L - 1 := by simp [a, pt]
      have ha1 : a 1 = B - 1 := by simp [a, pt]
      rw [ha0, ha1, hu'0] at hh
      exact ⟨by omega, Or.inr (Or.inr ⟨by omega, Or.inl ⟨hh.2.2, hbottom⟩⟩)⟩
    · simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨by simp only [hu'0, hu'1]; omega,
          Or.inr (Or.inr ⟨by rw [hu'0], Or.inl ⟨hu'1, hbottom⟩⟩)⟩
      · exact ⟨by omega, Or.inl rfl⟩
  · let u' : Site 2 := u + Pi.single 1 1
    let a : Site 2 := pt (L - 1) (T + 1)
    have hu'0 : u' 0 = u 0 := by simp [u']
    have hu'1 : u' 1 = T + 1 := by simp [u', htop]
    obtain ⟨p, hp⟩ := exists_horizontal_walk a u' (by simp [a, pt, hu'0]; omega)
      (by simp [a, pt, hu'1])
    have hu'eq : u' - Pi.single 1 1 = u := by simp [u']
    have hadj : (LatticeModels.zdGraph 2).Adj u' u := by
      simpa only [hu'eq] using adj_sub_single_one u'
    refine ⟨a, p.append hadj.toWalk, by simp [a, pt], ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hh := hp z hz
      have ha0 : a 0 = L - 1 := by simp [a, pt]
      have ha1 : a 1 = T + 1 := by simp [a, pt]
      rw [ha0, ha1, hu'0] at hh
      exact ⟨by omega, Or.inr (Or.inr ⟨by omega, Or.inr ⟨hh.2.2, htop⟩⟩)⟩
    · simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨by simp only [hu'0, hu'1]; omega,
          Or.inr (Or.inr ⟨by rw [hu'0], Or.inr ⟨hu'1, htop⟩⟩)⟩
      · exact ⟨by omega, Or.inl rfl⟩

/-- Extend a point on the right boundary arc to the right side of the rectangle expanded
by one lattice step. -/
theorem exists_right_boundary_extension (L R B T c : ℤ) (u : Site 2)
    (hbox : L ≤ u 0 ∧ u 0 ≤ R ∧ B ≤ u 1 ∧ u 1 ≤ T)
    (hright : u 0 = R ∨ (c ≤ u 0 ∧ (u 1 = B ∨ u 1 = T))) :
    ∃ (a : Site 2) (p : (LatticeModels.zdGraph 2).Walk u a), a 0 = R + 1 ∧
      ∀ z ∈ p.support,
        (L - 1 ≤ z 0 ∧ z 0 ≤ R + 1 ∧ B - 1 ≤ z 1 ∧ z 1 ≤ T + 1) ∧
        (z = u ∨ z 0 = R + 1 ∨
          (u 0 ≤ z 0 ∧ ((z 1 = B - 1 ∧ u 1 = B) ∨ (z 1 = T + 1 ∧ u 1 = T)))) := by
  have hBT : B ≤ T := by omega
  rcases hright with hside | ⟨hc, hbottom | htop⟩
  · let a : Site 2 := pt (R + 1) (u 1)
    obtain ⟨p, hp⟩ := exists_horizontal_walk u a (by simp [a, pt]; omega) (by simp [a, pt])
    refine ⟨a, p, by simp [a, pt], ?_⟩
    intro z hz
    have hh := hp z hz
    have ha0 : a 0 = R + 1 := by simp [a, pt]
    rw [ha0] at hh
    refine ⟨by omega, ?_⟩
    by_cases hzside : z 0 = R + 1
    · exact Or.inr (Or.inl hzside)
    · left
      apply LatticeModels.Site.eq_iff_two.mpr
      constructor <;> omega
  · let u' : Site 2 := u - Pi.single 1 1
    let a : Site 2 := pt (R + 1) (B - 1)
    have hu'0 : u' 0 = u 0 := by simp [u']
    have hu'1 : u' 1 = B - 1 := by simp [u', hbottom]
    obtain ⟨p, hp⟩ := exists_horizontal_walk u' a (by simp [a, pt, hu'0]; omega)
      (by simp [a, pt, hu'1])
    have hadj : (LatticeModels.zdGraph 2).Adj u u' := adj_sub_single_one u
    refine ⟨a, hadj.toWalk.append p, by simp [a, pt], ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨by omega, Or.inl rfl⟩
      · exact ⟨by simp only [hu'0, hu'1]; omega,
          Or.inr (Or.inr ⟨by rw [hu'0], Or.inl ⟨hu'1, hbottom⟩⟩)⟩
    · have hh := hp z hz
      have ha0 : a 0 = R + 1 := by simp [a, pt]
      rw [ha0, hu'0, hu'1] at hh
      exact ⟨by omega, Or.inr (Or.inr ⟨by omega, Or.inl ⟨hh.2.2, hbottom⟩⟩)⟩
  · let u' : Site 2 := u + Pi.single 1 1
    let a : Site 2 := pt (R + 1) (T + 1)
    have hu'0 : u' 0 = u 0 := by simp [u']
    have hu'1 : u' 1 = T + 1 := by simp [u', htop]
    obtain ⟨p, hp⟩ := exists_horizontal_walk u' a (by simp [a, pt, hu'0]; omega)
      (by simp [a, pt, hu'1])
    have hu'eq : u' - Pi.single 1 1 = u := by simp [u']
    have hadj : (LatticeModels.zdGraph 2).Adj u u' := by
      have hh : (LatticeModels.zdGraph 2).Adj u' u := by
        simpa only [hu'eq] using adj_sub_single_one u'
      exact hh.symm
    refine ⟨a, hadj.toWalk.append p, by simp [a, pt], ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨by omega, Or.inl rfl⟩
      · exact ⟨by simp only [hu'0, hu'1]; omega,
          Or.inr (Or.inr ⟨by rw [hu'0], Or.inr ⟨hu'1, htop⟩⟩)⟩
    · have hh := hp z hz
      have ha0 : a 0 = R + 1 := by simp [a, pt]
      rw [ha0, hu'0, hu'1] at hh
      exact ⟨by omega, Or.inr (Or.inr ⟨by omega, Or.inr ⟨hh.2.2, htop⟩⟩)⟩

end Sandpile.External.RSW
