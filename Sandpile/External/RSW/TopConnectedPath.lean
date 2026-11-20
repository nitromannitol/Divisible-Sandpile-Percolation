import Sandpile.External.RSW.CentralCorridorExit
import Sandpile.External.RSW.KSTPathInclusion
import Sandpile.External.RSW.BondWalk
import Sandpile.External.RSW.TranslatedArm

/-!
# Connecting an inner path to the top

A path arriving from the top between two KST paths either meets one of them or supplies
a new KST path through the central interval.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- An open KST path joined to the top side of its ambient rectangle. -/
def kstTopConnectedEvent (W n m : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  let Q := centeredPlaneRectangle W n
  {ω | ∃ (a b x d : Q) (p : (rectangleGraph Q).Walk a b)
      (q : (rectangleGraph Q).Walk x d),
    IsKSTPath m p ∧ x ∈ p.support ∧ (d : Site 2) 1 = n ∧
    IsBondOpenWalk ω p ∧ IsBondOpenWalk ω q}

/-- Two separated KST paths and an open path arriving between them from the top yield
an open KST path connected to the top. -/
theorem kstTopConnectedEvent_of_separated_paths {W n m : ℕ}
    (hm : 0 < m) (hW : m + m / 12 ≤ W) (hmn : m ≤ n)
    {ω : Sym2 (Site 2) → Bool}
    {a₁ b₁ a₂ b₂ u v : centeredPlaneRectangle W n}
    (p₁ : (rectangleGraph (centeredPlaneRectangle W n)).Walk a₁ b₁)
    (p₂ : (rectangleGraph (centeredPlaneRectangle W n)).Walk a₂ b₂)
    (r : (rectangleGraph (centeredPlaneRectangle W n)).Walk u v)
    (hp₁ : IsKSTPath m p₁) (hp₂ : IsKSTPath m p₂)
    (ho₁ : IsBondOpenWalk ω p₁) (ho₂ : IsBondOpenWalk ω p₂) (hor : IsBondOpenWalk ω r)
    (ha₁ : (a₁ : Site 2) 0 ≤ -(3 * ((m / 64 : ℕ) : ℤ)))
    (hb₁ : (b₁ : Site 2) 0 ≤ -(3 * ((m / 64 : ℕ) : ℤ)))
    (ha₂ : 3 * ((m / 64 : ℕ) : ℤ) ≤ (a₂ : Site 2) 0)
    (hb₂ : 3 * ((m / 64 : ℕ) : ℤ) ≤ (b₂ : Site 2) 0)
    (hu : (u : Site 2) 1 = -(m : ℤ) ∧
      -(3 * ((m / 64 : ℕ) : ℤ)) ≤ (u : Site 2) 0 ∧
      (u : Site 2) 0 ≤ 3 * ((m / 64 : ℕ) : ℤ))
    (hv : (v : Site 2) 1 = n)
    (hrBottom : ∀ z ∈ r.support, -(m : ℤ) ≤ (z : Site 2) 1) :
    ω ∈ kstTopConnectedEvent W n m := by
  let Q := centeredPlaneRectangle W n
  let α : ℤ := (m / 64 : ℕ)
  let β : ℤ := (m / 12 : ℕ)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 5 * α ≤ β := by dsimp only [α, β]; exact_mod_cast five_arm_offsets_le_bridge_offset m
  have hW' : (m : ℤ) + β ≤ W := by dsimp only [β]; exact_mod_cast hW
  have hmn' : (m : ℤ) ≤ n := by exact_mod_cast hmn
  let g : rectangleGraph Q →g LatticeModels.zdGraph 2 := ⟨Subtype.val, fun h => by
    rw [← lattice_eq_zdGraph]
    exact h⟩
  have hbox {a b : Q} (p : (rectangleGraph Q).Walk a b) (hp : IsKSTPath m p) :
      ∀ z ∈ (p.map g).support,
        -((m + m / 12 : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
          -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp (hp.2.2.2.2.2.2.2 z' hz')
  have hbottom : ∀ z ∈ (r.map g).support, -(m : ℤ) ≤ z 1 := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact hrBottom z' hz'
  have hstart : (g u) 1 = -(m : ℤ) ∧ -3 * α ≤ (g u) 0 ∧ (g u) 0 ≤ 3 * α := by
    change (u : Site 2) 1 = -(m : ℤ) ∧ -3 * α ≤ (u : Site 2) 0 ∧ (u : Site 2) 0 ≤ 3 * α
    dsimp only [α] at *
    omega
  have hEnd : (m : ℤ) ≤ (g v) 1 := by
    change (m : ℤ) ≤ (v : Site 2) 1
    rw [hv]
    exact hmn'
  have hleftA : (g a₁) 1 = m ∧ -β ≤ (g a₁) 0 ∧ (g a₁) 0 ≤ -3 * α := by
    change (a₁ : Site 2) 1 = m ∧ -β ≤ (a₁ : Site 2) 0 ∧ (a₁ : Site 2) 0 ≤ -3 * α
    dsimp only [α, β] at *
    exact ⟨hp₁.2.1, hp₁.2.2.2.1, by omega⟩
  have hleftB : (g b₁) 1 = -(m : ℤ) ∧ -β ≤ (g b₁) 0 ∧ (g b₁) 0 ≤ -3 * α := by
    change (b₁ : Site 2) 1 = -(m : ℤ) ∧ -β ≤ (b₁ : Site 2) 0 ∧ (b₁ : Site 2) 0 ≤ -3 * α
    dsimp only [α, β] at *
    exact ⟨hp₁.2.2.1, hp₁.2.2.2.2.2.1, by omega⟩
  have hrightA : (g a₂) 1 = m ∧ 3 * α ≤ (g a₂) 0 ∧ (g a₂) 0 ≤ β := by
    change (a₂ : Site 2) 1 = m ∧ 3 * α ≤ (a₂ : Site 2) 0 ∧ (a₂ : Site 2) 0 ≤ β
    exact ⟨hp₂.2.1, ha₂, hp₂.2.2.2.2.1⟩
  have hrightB : (g b₂) 1 = -(m : ℤ) ∧ 3 * α ≤ (g b₂) 0 ∧ (g b₂) 0 ≤ β := by
    change (b₂ : Site 2) 1 = -(m : ℤ) ∧ 3 * α ≤ (b₂ : Site 2) 0 ∧ (b₂ : Site 2) 0 ≤ β
    exact ⟨hp₂.2.2.1, hb₂, hp₂.2.2.2.2.2.2.1⟩
  have hcases := central_corridor_first_exit
    (L := -((m + m / 12 : ℕ) : ℤ)) (R := ((m + m / 12 : ℕ) : ℤ))
    (B := -(m : ℤ)) (T := m) (lc := -β) (ld := -3 * α) (rc := 3 * α) (rd := β)
    (by push_cast; omega) (by push_cast; omega) (by omega)
    (by omega) (by omega) (by omega)
    (p₁.map g) (p₂.map g) (r.map g) (hbox p₁ hp₁) (hbox p₂ hp₂)
    hleftA hleftB hrightA hrightB hstart hEnd hbottom
  rcases hcases with hhit₁ | hhit₂ | ⟨c, q, hcT, hcL, hcR, hqbox, hqs, hqe⟩
  · obtain ⟨z, hz₁, hzr⟩ := hhit₁
    rw [SimpleGraph.Walk.support_map] at hz₁ hzr
    obtain ⟨x, hx₁, hx⟩ := List.mem_map.mp hz₁
    obtain ⟨y, hyr, hy⟩ := List.mem_map.mp hzr
    have hxy : x = y := Subtype.ext (hx.trans hy.symm)
    subst y
    obtain ⟨s, hs, _⟩ := exists_openWalk_of_mem_support r hor hyr r.end_mem_support
    exact ⟨a₁, b₁, x, v, p₁, s, hp₁, hx₁, hv, ho₁, hs⟩
  · obtain ⟨z, hz₂, hzr⟩ := hhit₂
    rw [SimpleGraph.Walk.support_map] at hz₂ hzr
    obtain ⟨x, hx₂, hx⟩ := List.mem_map.mp hz₂
    obtain ⟨y, hyr, hy⟩ := List.mem_map.mp hzr
    have hxy : x = y := Subtype.ext (hx.trans hy.symm)
    subst y
    obtain ⟨s, hs, _⟩ := exists_openWalk_of_mem_support r hor hyr r.end_mem_support
    exact ⟨a₂, b₂, x, v, p₂, s, hp₂, hx₂, hv, ho₂, hs⟩
  · let qL := q.transfer (lattice 2) (fun e he => by
      rw [lattice_eq_zdGraph]
      exact q.edges_subset_edgeSet he)
    have hqLsupport : qL.support = q.support := by
      simp only [qL, SimpleGraph.Walk.support_transfer]
    have hqLedges : qL.edges = q.edges := by
      simp only [qL, SimpleGraph.Walk.edges_transfer]
    have hqQ : ∀ z ∈ qL.support, z ∈ (Q : Set (Site 2)) := by
      intro z hz
      rw [hqLsupport] at hz
      have hh := hqbox z hz
      apply (mem_centeredPlaneRectangle _ _ z).mpr
      push_cast at hh
      omega
    let q' := qL.induce (Q : Set (Site 2)) hqQ
    have hqopen : IsBondOpenWalk ω q' := by
      apply (isBondOpenWalk_iff_edges ω q').mpr
      intro e he
      rw [SimpleGraph.Walk.map_induce] at he
      have he' : e ∈ q.edges := hqLedges ▸ he
      have hr := hqe e he'
      rw [SimpleGraph.Walk.edges_map] at hr
      obtain ⟨e', he', heq⟩ := List.mem_map.mp hr
      change Sym2.map Subtype.val e' = e at heq
      rw [← heq]
      exact (isBondOpenWalk_iff_local_edges ω r).mp hor e' he' 
    have hcOuter : c ∈ (r.map g).support := hqs c q.end_mem_support
    rw [SimpleGraph.Walk.support_map] at hcOuter
    obtain ⟨x, hxr, hx⟩ := List.mem_map.mp hcOuter
    have heq : x = ⟨c, hqQ c qL.end_mem_support⟩ := Subtype.ext hx
    subst x
    obtain ⟨s, hs, _⟩ := exists_openWalk_of_mem_support r hor hxr r.end_mem_support
    let p := q'.reverse.bypass
    have hp : IsKSTPath m p := by
      refine ⟨q'.reverse.bypass_isPath, hcT, hu.1, hcL, hcR, ?_, ?_, ?_⟩
      · dsimp only [α, β] at *
        omega
      · dsimp only [α, β] at *
        omega
      · intro z hz
        have hz' := q'.reverse.support_bypass_subset_support hz
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz'
        have hzm : (z : Site 2) ∈ (q'.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom).support := by
          rw [SimpleGraph.Walk.support_map]
          exact List.mem_map.mpr ⟨z, hz', rfl⟩
        rw [SimpleGraph.Walk.map_induce] at hzm
        have hzm' : (z : Site 2) ∈ q.support := hqLsupport ▸ hzm
        exact (mem_centeredPlaneRectangle _ _ _).mpr (hqbox _ hzm')
    have hopen : IsBondOpenWalk ω p := hqopen.reverse.bypass
    exact ⟨_, _, _, v, p, s, hp, p.start_mem_support, hv, hopen, hs⟩

end Sandpile.External.RSW
