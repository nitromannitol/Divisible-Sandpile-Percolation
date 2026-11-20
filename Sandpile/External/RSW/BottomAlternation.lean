import Sandpile.External.RSW.BottomAlternationExtension

/-!
# Alternating paths with endpoints on the bottom side

Two paths in a rectangle whose four bottom endpoints alternate must intersect. The paths
are extended along disjoint rows outside the rectangle to produce perpendicular crossings.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Paths joining alternating pairs of bottom boundary vertices meet. -/
theorem bottom_alternating_paths_intersect {L R B T : ℤ}
    {a b c d : Site 2} (p : (LatticeModels.zdGraph 2).Walk a c)
    (q : (LatticeModels.zdGraph 2).Walk b d)
    (hp : ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hq : ∀ z ∈ q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 1 = B) (hb : b 1 = B) (hc : c 1 = B) (hd : d 1 = B)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0) :
    ∃ z ∈ p.support, z ∈ q.support := by
  classical
  by_contra hdis
  push Not at hdis
  have haBox := hp a p.start_mem_support
  have hcBox := hp c p.end_mem_support
  have hbBox := hq b q.start_mem_support
  have hdBox := hq d q.end_mem_support
  have hBT : B ≤ T := by omega
  obtain ⟨l, hl⟩ := exists_bottom_left_extension_two L B a haBox.1 ha
  obtain ⟨r, hr⟩ := exists_bottom_right_extension_two R B c hcBox.2.1 hc
  obtain ⟨t, ht⟩ := exists_bottom_right_top_extension R B T d hdBox.2.1 hd hBT
  let bottom : Site 2 := pt (b 0) (B - 3)
  obtain ⟨s, hs⟩ := exists_vertical_walk bottom b (by simp [bottom, pt])
    (by simp [bottom, pt, hb])
  let H := (l.append p).append r
  let V := (s.append q).append t
  have hHshape {z : Site 2} (hz : z ∈ H.support) :
      z ∈ l.support ∨ z ∈ p.support ∨ z ∈ r.support := by
    change z ∈ ((l.append p).append r).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      exact hz.imp_right Or.inl
    · exact Or.inr (Or.inr hz)
  have hVshape {z : Site 2} (hz : z ∈ V.support) :
      z ∈ s.support ∨ z ∈ q.support ∨ z ∈ t.support := by
    change z ∈ ((s.append q).append t).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      exact hz.imp_right Or.inl
    · exact Or.inr (Or.inr hz)
  have hHbox : ∀ z ∈ H.support, L - 1 ≤ z 0 ∧ z 0 ≤ R + 1 ∧ B - 3 ≤ z 1 ∧ z 1 ≤ T + 1 := by
    intro z hz
    rcases hHshape hz with hz | hz | hz
    · rcases hl z hz with ⟨h0, h1, h2⟩ | ⟨h1, h0, h2⟩ <;> omega
    · have hh := hp z hz
      omega
    · rcases hr z hz with ⟨h0, h1, h2⟩ | ⟨h1, h0, h2⟩ <;> omega
  have hVbox : ∀ z ∈ V.support, L - 1 ≤ z 0 ∧ z 0 ≤ R + 1 ∧ B - 3 ≤ z 1 ∧ z 1 ≤ T + 1 := by
    intro z hz
    rcases hVshape hz with hz | hz | hz
    · have hh := hs z hz
      simp only [bottom, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, hb] at hh
      omega
    · have hh := hq z hz
      omega
    · rcases ht z hz with ⟨h0, h1, h2⟩ | ⟨h1, h0, h2⟩ | ⟨h0, h1, h2⟩ <;> omega
  have hleft : (pt (L - 1) (B - 2)) 0 = L - 1 := by simp [pt]
  have hright : (pt (R + 1) (B - 2)) 0 = R + 1 := by simp [pt]
  have hbottom : bottom 1 = B - 3 := by simp [bottom, pt]
  have htop : (pt (R + 1) (T + 1)) 1 = T + 1 := by simp [pt]
  obtain ⟨z, hzH, hzV⟩ := exists_mem_support_of_crossing H V hHbox hVbox
    hleft hright hbottom htop
  have hs' (z : Site 2) (hz : z ∈ s.support) :
      z 0 = b 0 ∧ B - 3 ≤ z 1 ∧ z 1 ≤ B := by
    have hh := hs z hz
    simpa only [bottom, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hb] using hh
  rcases hHshape hzH with hzl | hzp | hzr
  · rcases hVshape hzV with hzs | hzq | hzt
    · rcases hl z hzl with ⟨h0, _, _⟩ | ⟨_, _, h0⟩ <;>
        have hh := hs' z hzs <;> omega
    · have hh := hq z hzq
      rcases hl z hzl with ⟨h0, h1, h2⟩ | ⟨h1, _, _⟩
      · have he : z = a := LatticeModels.Site.eq_iff_two.mpr ⟨h0, by omega⟩
        subst z
        exact hdis a p.start_mem_support hzq
      · omega
    · rcases hl z hzl with ⟨h0, h1, h2⟩ | ⟨h1, h0, h2⟩ <;>
        rcases ht z hzt with ⟨ht0, ht1, ht2⟩ | ⟨ht1, ht0, ht2⟩ | ⟨ht0, ht1, ht2⟩ <;> omega
  · rcases hVshape hzV with hzs | hzq | hzt
    · have hh := hs' z hzs
      have hpz := hp z hzp
      have he : z = b := LatticeModels.Site.eq_iff_two.mpr ⟨hh.1, by omega⟩
      subst z
      exact hdis b hzp q.start_mem_support
    · exact hdis z hzp hzq
    · have hpz := hp z hzp
      rcases ht z hzt with ⟨h0, h1, h2⟩ | ⟨h1, _, _⟩ | ⟨h0, _, _⟩
      · have he : z = d := LatticeModels.Site.eq_iff_two.mpr ⟨h0, by omega⟩
        subst z
        exact hdis d hzp q.end_mem_support
      · omega
      · omega
  · rcases hVshape hzV with hzs | hzq | hzt
    · rcases hr z hzr with ⟨h0, _, _⟩ | ⟨_, h0, _⟩ <;>
        have hh := hs' z hzs <;> omega
    · have hh := hq z hzq
      rcases hr z hzr with ⟨h0, h1, h2⟩ | ⟨h1, _, _⟩
      · have he : z = c := LatticeModels.Site.eq_iff_two.mpr ⟨h0, by omega⟩
        subst z
        exact hdis c p.end_mem_support hzq
      · omega
    · rcases hr z hzr with ⟨h0, h1, h2⟩ | ⟨h1, h0, h2⟩ <;>
        rcases ht z hzt with ⟨ht0, ht1, ht2⟩ | ⟨ht1, ht0, ht2⟩ | ⟨ht0, ht1, ht2⟩ <;> omega

end Sandpile.External.RSW
