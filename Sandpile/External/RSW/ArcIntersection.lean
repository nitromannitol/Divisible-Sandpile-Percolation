import Sandpile.External.RSW.BoundaryExtension

/-!
# Intersection of alternating boundary paths

A top-to-bottom path with endpoints in a central boundary segment intersects every
left-to-right path whose endpoints lie on the two outer boundary arcs.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Paths joining alternating boundary arcs of a lattice rectangle meet. -/
theorem alternating_boundary_paths_intersect {L R B T c d : ℤ}
    (hLc : L < c) (hdR : d < R) (hBT : B < T)
    {a b u v : Site 2} (p : (LatticeModels.zdGraph 2).Walk a b)
    (r : (LatticeModels.zdGraph 2).Walk u v)
    (hp : ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hr : ∀ z ∈ r.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 1 = T ∧ c ≤ a 0 ∧ a 0 ≤ d)
    (hb : b 1 = B ∧ c ≤ b 0 ∧ b 0 ≤ d)
    (hu : u 0 = L ∨ (u 0 ≤ c ∧ (u 1 = B ∨ u 1 = T)))
    (hv : v 0 = R ∨ (d ≤ v 0 ∧ (v 1 = B ∨ v 1 = T))) :
    ∃ z ∈ p.support, z ∈ r.support := by
  classical
  by_contra hdis
  push Not at hdis
  have hU := hr u r.start_mem_support
  have hV := hr v r.end_mem_support
  obtain ⟨x, l, hx, hl⟩ := exists_left_boundary_extension L R B T c u hU hu
  obtain ⟨y, s, hy, hs⟩ := exists_right_boundary_extension L R B T d v hV hv
  let bot : Site 2 := b - Pi.single 1 1
  let top : Site 2 := a + Pi.single 1 1
  have hbot0 : bot 0 = b 0 := by simp [bot]
  have hbot1 : bot 1 = B - 1 := by simp [bot, hb.1]
  have htop0 : top 0 = a 0 := by simp [top]
  have htop1 : top 1 = T + 1 := by simp [top, ha.1]
  have htop_eq : top - Pi.single 1 1 = a := by simp [top]
  have hbot_adj : (LatticeModels.zdGraph 2).Adj bot b := (adj_sub_single_one b).symm
  have htop_adj : (LatticeModels.zdGraph 2).Adj a top := by
    have hh : (LatticeModels.zdGraph 2).Adj top a := by
      simpa only [htop_eq] using adj_sub_single_one top
    exact hh.symm
  let V := hbot_adj.toWalk.append (p.reverse.append htop_adj.toWalk)
  let H := (l.append r).append s
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
    · rw [hbot0, hbot1]; omega
    · have hh := hp z hz
      omega
    · rw [htop0, htop1]; omega
  have hHbox : ∀ z ∈ H.support, L - 1 ≤ z 0 ∧ z 0 ≤ R + 1 ∧ B - 1 ≤ z 1 ∧ z 1 ≤ T + 1 := by
    intro z hz
    change z ∈ ((l.append r).append s).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact (hl z hz).1
      · have hh := hr z hz
        omega
    · exact (hs z hz).1
  have hPleft : ∀ z ∈ p.support, z ∉ l.support := by
    intro z hzp hzl
    have hzpbox := hp z hzp
    rcases (hl z hzl).2 with hz | hz | ⟨_, ⟨hz, _⟩ | ⟨hz, _⟩⟩
    · subst z
      exact hdis u hzp r.start_mem_support
    · omega
    · omega
    · omega
  have hPright : ∀ z ∈ p.support, z ∉ s.support := by
    intro z hzp hzs
    have hzpbox := hp z hzp
    rcases (hs z hzs).2 with hz | hz | ⟨_, ⟨hz, _⟩ | ⟨hz, _⟩⟩
    · subst z
      exact hdis v hzp r.end_mem_support
    · omega
    · omega
    · omega
  have hBotLeft : bot ∉ l.support := by
    intro hz
    rcases (hl bot hz).2 with he | he | ⟨he, ⟨hey, huy⟩ | ⟨hey, huy⟩⟩
    · have hu1 := congrArg (fun z : Site 2 => z 1) he
      omega
    · omega
    · have heq : u = b := by
        apply LatticeModels.Site.eq_iff_two.mpr
        constructor <;> omega
      exact hdis b p.end_mem_support (heq ▸ r.start_mem_support)
    · omega
  have hTopLeft : top ∉ l.support := by
    intro hz
    rcases (hl top hz).2 with he | he | ⟨he, ⟨hey, huy⟩ | ⟨hey, huy⟩⟩
    · have hu1 := congrArg (fun z : Site 2 => z 1) he
      omega
    · omega
    · omega
    · have heq : u = a := by
        apply LatticeModels.Site.eq_iff_two.mpr
        constructor <;> omega
      exact hdis a p.start_mem_support (heq ▸ r.start_mem_support)
  have hBotRight : bot ∉ s.support := by
    intro hz
    rcases (hs bot hz).2 with he | he | ⟨he, ⟨hey, hvy⟩ | ⟨hey, hvy⟩⟩
    · have hv1 := congrArg (fun z : Site 2 => z 1) he
      omega
    · omega
    · have heq : v = b := by
        apply LatticeModels.Site.eq_iff_two.mpr
        constructor <;> omega
      exact hdis b p.end_mem_support (heq ▸ r.end_mem_support)
    · omega
  have hTopRight : top ∉ s.support := by
    intro hz
    rcases (hs top hz).2 with he | he | ⟨he, ⟨hey, hvy⟩ | ⟨hey, hvy⟩⟩
    · have hv1 := congrArg (fun z : Site 2 => z 1) he
      omega
    · omega
    · omega
    · have heq : v = a := by
        apply LatticeModels.Site.eq_iff_two.mpr
        constructor <;> omega
      exact hdis a p.start_mem_support (heq ▸ r.end_mem_support)
  obtain ⟨z, hzH, hzV⟩ := exists_mem_support_of_crossing H V hHbox hVbox hx hy hbot1 htop1
  change z ∈ ((l.append r).append s).support at hzH
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzH
  have hzHor : z ∈ l.support ∨ z ∈ r.support ∨ z ∈ s.support := by
    rcases hzH with hz | hz
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      exact hz.imp_right Or.inl
    · exact Or.inr (Or.inr hz)
  rcases hVshape hzV with rfl | hzp | rfl
  · rcases hzHor with hz | hz | hz
    · exact hBotLeft hz
    · have hh := hr bot hz
      omega
    · exact hBotRight hz
  · rcases hzHor with hz | hz | hz
    · exact hPleft z hzp hz
    · exact hdis z hzp hz
    · exact hPright z hzp hz
  · rcases hzHor with hz | hz | hz
    · exact hTopLeft hz
    · have hh := hr top hz
      omega
    · exact hTopRight hz

end Sandpile.External.RSW
