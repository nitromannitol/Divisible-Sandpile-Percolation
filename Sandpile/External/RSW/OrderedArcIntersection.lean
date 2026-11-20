import Sandpile.External.RSW.BoundaryExtension

/-!
# Boundary arcs with ordered endpoints

A vertical rectangle crossing meets a walk from its upper-left boundary arc to
its lower-right boundary arc, with the arcs ordered by the crossing endpoints.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A vertical crossing meets a walk joining the opposite boundary arcs. -/
theorem vertical_walk_intersects_ordered_boundary_walk {L R B T : ℤ}
    (hBT : B < T) {a b u v : Site 2}
    (p : (LatticeModels.zdGraph 2).Walk a b)
    (q : (LatticeModels.zdGraph 2).Walk u v)
    (hp : ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hq : ∀ z ∈ q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 1 = T) (hb : b 1 = B)
    (hu : u 0 = L ∨ (u 1 = T ∧ u 0 ≤ a 0) ∨ (u 1 = B ∧ u 0 ≤ b 0))
    (hv : v 0 = R ∨ (v 1 = B ∧ b 0 ≤ v 0) ∨ (v 1 = T ∧ a 0 ≤ v 0)) :
    ∃ z ∈ p.support, z ∈ q.support := by
  classical
  by_contra hdis
  push Not at hdis
  have hU := hq u q.start_mem_support
  have hV := hq v q.end_mem_support
  have htop : u 1 = T → u 0 ≤ a 0 := by
    intro hrow
    rcases hu with he | he | he
    · have h := hp a p.start_mem_support
      omega
    · exact he.2
    · omega
  have hbottom : v 1 = B → b 0 ≤ v 0 := by
    intro hrow
    rcases hv with he | he | he
    · have h := hp b p.end_mem_support
      omega
    · exact he.2
    · omega
  have htopOther : u 1 = B → u 0 ≤ b 0 := by
    intro hrow
    rcases hu with he | he | he
    · have h := hp b p.end_mem_support
      omega
    · omega
    · exact he.2
  have hbottomOther : v 1 = T → a 0 ≤ v 0 := by
    intro hrow
    rcases hv with he | he | he
    · have h := hp a p.start_mem_support
      omega
    · omega
    · exact he.2
  have huArc : u 0 = L ∨ (u 0 ≤ u 0 ∧ (u 1 = B ∨ u 1 = T)) := by
    rcases hu with he | he | he
    · exact Or.inl he
    · exact Or.inr ⟨le_rfl, Or.inr he.1⟩
    · exact Or.inr ⟨le_rfl, Or.inl he.1⟩
  have hvArc : v 0 = R ∨ (v 0 ≤ v 0 ∧ (v 1 = B ∨ v 1 = T)) := by
    rcases hv with he | he | he
    · exact Or.inl he
    · exact Or.inr ⟨le_rfl, Or.inl he.1⟩
    · exact Or.inr ⟨le_rfl, Or.inr he.1⟩
  obtain ⟨x, l, hx, hl⟩ := exists_left_boundary_extension L R B T (u 0) u hU huArc
  obtain ⟨y, r, hy, hr⟩ := exists_right_boundary_extension L R B T (v 0) v hV hvArc
  let bot : Site 2 := b - Pi.single 1 1
  let top : Site 2 := a + Pi.single 1 1
  have hbot0 : bot 0 = b 0 := by simp [bot]
  have hbot1 : bot 1 = B - 1 := by simp [bot, hb]
  have htop0 : top 0 = a 0 := by simp [top]
  have htop1 : top 1 = T + 1 := by simp [top, ha]
  have htop_eq : top - Pi.single 1 1 = a := by simp [top]
  have hbot_adj : (LatticeModels.zdGraph 2).Adj bot b := (adj_sub_single_one b).symm
  have htop_adj : (LatticeModels.zdGraph 2).Adj a top := by
    have hh : (LatticeModels.zdGraph 2).Adj top a := by
      simpa only [htop_eq] using adj_sub_single_one top
    exact hh.symm
  let V := hbot_adj.toWalk.append (p.reverse.append htop_adj.toWalk)
  let H := (l.append q).append r
  have hVshape {z : Site 2} (hz : z ∈ V.support) :
      z = bot ∨ z ∈ p.support ∨ z = top := by
    change z ∈ (hbot_adj.toWalk.append (p.reverse.append htop_adj.toWalk)).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl p.end_mem_support)
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
        exact Or.inr (Or.inl hz)
      · simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact Or.inr (Or.inl p.start_mem_support)
        · exact Or.inr (Or.inr rfl)
  have hVbox : ∀ z ∈ V.support, L - 1 ≤ z 0 ∧ z 0 ≤ R + 1 ∧ B - 1 ≤ z 1 ∧ z 1 ≤ T + 1 := by
    intro z hz
    rcases hVshape hz with rfl | hz | rfl
    · rw [hbot0, hbot1]; have h := hp b p.end_mem_support; omega
    · have h := hp z hz; omega
    · rw [htop0, htop1]; have h := hp a p.start_mem_support; omega
  have hHbox : ∀ z ∈ H.support, L - 1 ≤ z 0 ∧ z 0 ≤ R + 1 ∧ B - 1 ≤ z 1 ∧ z 1 ≤ T + 1 := by
    intro z hz
    change z ∈ ((l.append q).append r).support at hz
    simp only [SimpleGraph.Walk.mem_support_append_iff, or_assoc] at hz
    rcases hz with hz | hz | hz
    · exact (hl z hz).1
    · have h := hq z hz; omega
    · exact (hr z hz).1
  obtain ⟨z, hzH, hzV⟩ := exists_mem_support_of_crossing H V hHbox hVbox hx hy hbot1 htop1
  change z ∈ ((l.append q).append r).support at hzH
  simp only [SimpleGraph.Walk.mem_support_append_iff, or_assoc] at hzH
  rcases hVshape hzV with rfl | hzp | rfl
  · rcases hzH with hzl | hzq | hzr
    · rcases (hl bot hzl).2 with he | he | ⟨h0, ⟨he, huB⟩ | ⟨he, _⟩⟩
      · have h := congrArg (fun z : Site 2 => z 1) he; omega
      · have h := hp b p.end_mem_support; omega
      · have horder := htopOther huB
        have he : b = u := LatticeModels.Site.eq_iff_two.mpr ⟨by omega, by omega⟩
        exact hdis b p.end_mem_support (he ▸ q.start_mem_support)
      · omega
    · have h := hq bot hzq; omega
    · rcases (hr bot hzr).2 with he | he | ⟨h0, ⟨h1, hvB⟩ | ⟨h1, _⟩⟩
      · have h := congrArg (fun z : Site 2 => z 1) he; omega
      · have h := hp b p.end_mem_support; omega
      · have horder := hbottom hvB
        have he : b = v := LatticeModels.Site.eq_iff_two.mpr ⟨by omega, by omega⟩
        exact hdis b p.end_mem_support (he ▸ q.end_mem_support)
      · omega
  · rcases hzH with hzl | hzq | hzr
    · rcases (hl z hzl).2 with he | he | ⟨_, ⟨h1, _⟩ | ⟨h1, _⟩⟩
      · subst z; exact hdis u hzp q.start_mem_support
      · have h := hp z hzp; omega
      · have h := hp z hzp; omega
      · have h := hp z hzp; omega
    · exact hdis z hzp hzq
    · rcases (hr z hzr).2 with he | he | ⟨_, ⟨h1, _⟩ | ⟨h1, _⟩⟩
      · subst z; exact hdis v hzp q.end_mem_support
      · have h := hp z hzp; omega
      · have h := hp z hzp; omega
      · have h := hp z hzp; omega
  · rcases hzH with hzl | hzq | hzr
    · rcases (hl top hzl).2 with he | he | ⟨h0, ⟨h1, _⟩ | ⟨h1, huT⟩⟩
      · have h := congrArg (fun z : Site 2 => z 1) he; omega
      · have h := hp a p.start_mem_support; omega
      · omega
      · have horder := htop huT
        have he : a = u := LatticeModels.Site.eq_iff_two.mpr ⟨by omega, by omega⟩
        exact hdis a p.start_mem_support (he ▸ q.start_mem_support)
    · have h := hq top hzq; omega
    · rcases (hr top hzr).2 with he | he | ⟨h0, ⟨h1, _⟩ | ⟨h1, hvT⟩⟩
      · have h := congrArg (fun z : Site 2 => z 1) he; omega
      · have h := hp a p.start_mem_support; omega
      · omega
      · have horder := hbottomOther hvT
        have he : a = v := LatticeModels.Site.eq_iff_two.mpr ⟨by omega, by omega⟩
        exact hdis a p.start_mem_support (he ▸ q.end_mem_support)

end Sandpile.External.RSW
