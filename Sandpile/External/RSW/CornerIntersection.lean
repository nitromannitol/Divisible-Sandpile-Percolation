import Sandpile.External.RSW.TopBoundaryExtension
import Sandpile.External.RSW.BottomBoundaryExtension
import Sandpile.External.RSW.BoundaryExtension

/-!
# Intersection of corner connections

Two paths joining opposite upper boundary arcs to the opposite halves of the bottom
boundary intersect. Paths are extended outside the rectangle to apply lattice crossing
intersection.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Opposite corner connections meet when their upper endpoints are above the bottom side. -/
theorem corner_boundary_paths_intersect {L R B T : ℤ}
    (hL : L < 0) (hR : 0 < R) (hBT : B < T)
    {a b u v : Site 2} (p : (LatticeModels.zdGraph 2).Walk a b)
    (q : (LatticeModels.zdGraph 2).Walk u v)
    (hp : ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hq : ∀ z ∈ q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : (a 0 = L ∨ (a 1 = T ∧ a 0 < 0)) ∧ B < a 1)
    (hb : b 1 = B ∧ 0 < b 0)
    (hu : u 1 = B ∧ u 0 < 0)
    (hv : (v 0 = R ∨ (v 1 = T ∧ 0 < v 0)) ∧ B < v 1) :
    ∃ z ∈ p.support, z ∈ q.support := by
  classical
  by_contra hdis
  push Not at hdis
  have haBox := hp a p.start_mem_support
  have hbBox := hp b p.end_mem_support
  have huBox := hq u q.start_mem_support
  have hvBox := hq v q.end_mem_support
  obtain ⟨topWalk, htopWalk⟩ := exists_top_left_boundary_extension L T a (by omega)
    haBox.1 haBox.2.2.2 (ha.1.imp_right fun h => ⟨h.1, le_of_lt h.2⟩)
  obtain ⟨leftWalk, hleftWalk⟩ := exists_bottom_left_boundary_extension L B u huBox.1 hu.1
  obtain ⟨right, rightWalk, hright, hrightWalk⟩ := exists_right_boundary_extension L R B T 0 v
    hvBox (hv.1.imp_right fun h => ⟨le_of_lt h.2, Or.inr h.1⟩)
  let bottom : Site 2 := b - Pi.single 1 1
  have hbot0 : bottom 0 = b 0 := by simp [bottom]
  have hbot1 : bottom 1 = B - 1 := by simp [bottom, hb.1]
  have hbotAdj : (LatticeModels.zdGraph 2).Adj bottom b := (adj_sub_single_one b).symm
  let V := hbotAdj.toWalk.append (p.reverse.append topWalk)
  let H := (leftWalk.append q).append rightWalk
  have hVshape {z : Site 2} (hz : z ∈ V.support) :
      z = bottom ∨ z ∈ p.support ∨ z ∈ topWalk.support := by
    change z ∈ (hbotAdj.toWalk.append (p.reverse.append topWalk)).support at hz
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
      · exact Or.inr (Or.inr hz)
  have hHshape {z : Site 2} (hz : z ∈ H.support) :
      z ∈ leftWalk.support ∨ z ∈ q.support ∨ z ∈ rightWalk.support := by
    change z ∈ ((leftWalk.append q).append rightWalk).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      exact hz.imp_right Or.inl
    · exact Or.inr (Or.inr hz)
  have hVbox : ∀ z ∈ V.support, L - 1 ≤ z 0 ∧ z 0 ≤ R + 1 ∧ B - 1 ≤ z 1 ∧ z 1 ≤ T + 1 := by
    intro z hz
    rcases hVshape hz with rfl | hz | hz
    · rw [hbot0, hbot1]; omega
    · have hh := hp z hz
      omega
    · rcases htopWalk z hz with rfl | ⟨h0, h1, h2⟩ | ⟨h1, h0, h2⟩
      · omega
      · omega
      · omega
  have hHbox : ∀ z ∈ H.support, L - 1 ≤ z 0 ∧ z 0 ≤ R + 1 ∧ B - 1 ≤ z 1 ∧ z 1 ≤ T + 1 := by
    intro z hz
    rcases hHshape hz with hz | hz | hz
    · rcases hleftWalk z hz with rfl | ⟨h1, h0, h2⟩ <;> omega
    · have hh := hq z hz
      omega
    · exact (hrightWalk z hz).1
  have htop1 : (pt 0 (T + 1)) 1 = T + 1 := by simp [pt]
  have hleft0 : (pt (L - 1) (B - 1)) 0 = L - 1 := by simp [pt]
  obtain ⟨z, hzH, hzV⟩ := exists_mem_support_of_crossing H V hHbox hVbox
    hleft0 hright hbot1 htop1
  rcases hVshape hzV with rfl | hzp | hzt
  · rcases hHshape hzH with hzl | hzq | hzr
    · rcases hleftWalk bottom hzl with he | ⟨he, h0, h1⟩
      · have hy := congrArg (fun z : Site 2 => z 1) he
        omega
      · omega
    · have hh := hq bottom hzq
      omega
    · rcases (hrightWalk bottom hzr).2 with he | he | ⟨h0, ⟨he, hvb⟩ | ⟨he, hvt⟩⟩
      · have hy := congrArg (fun z : Site 2 => z 1) he
        omega
      · omega
      · omega
      · omega
  · rcases hHshape hzH with hzl | hzq | hzr
    · rcases hleftWalk z hzl with rfl | ⟨he, _, _⟩
      · exact hdis z hzp q.start_mem_support
      · have hh := hp z hzp
        omega
    · exact hdis z hzp hzq
    · rcases (hrightWalk z hzr).2 with rfl | he | ⟨_, ⟨he, _⟩ | ⟨he, _⟩⟩
      · exact hdis z hzp q.end_mem_support
      · have hh := hp z hzp
        omega
      · have hh := hp z hzp
        omega
      · have hh := hp z hzp
        omega
  · rcases htopWalk z hzt with hza | ⟨hzx, hzlo, hzhi⟩ | ⟨hzy, hzlo, hzhi⟩
    · subst z
      rcases hHshape hzH with hzl | hzq | hzr
      · rcases hleftWalk a hzl with he | ⟨he, _, _⟩
        · subst a
          exact hdis u p.start_mem_support q.start_mem_support
        · omega
      · exact hdis a p.start_mem_support hzq
      · rcases (hrightWalk a hzr).2 with he | he | ⟨_, ⟨he, _⟩ | ⟨he, _⟩⟩
        · subst a
          exact hdis v p.start_mem_support q.end_mem_support
        · omega
        · omega
        · omega
    · rcases hHshape hzH with hzl | hzq | hzr
      · rcases hleftWalk z hzl with he | ⟨he, _, _⟩
        · have hx := congrArg (fun z : Site 2 => z 0) he
          omega
        · omega
      · have hh := hq z hzq
        omega
      · rcases (hrightWalk z hzr).2 with he | he | ⟨_, ⟨he, _⟩ | ⟨he, _⟩⟩
        · have hx := congrArg (fun z : Site 2 => z 0) he
          omega
        · omega
        · omega
        · omega
    · rcases hHshape hzH with hzl | hzq | hzr
      · rcases hleftWalk z hzl with he | ⟨he, _, _⟩
        · have hy := congrArg (fun z : Site 2 => z 1) he
          omega
        · omega
      · have hh := hq z hzq
        omega
      · rcases (hrightWalk z hzr).2 with he | he | ⟨h0, ⟨he, _⟩ | ⟨he, _⟩⟩
        · have hy := congrArg (fun z : Site 2 => z 1) he
          omega
        · omega
        · omega
        · rcases hv.1 with hvside | ⟨_, hvpos⟩
          · omega
          · omega

end Sandpile.External.RSW
