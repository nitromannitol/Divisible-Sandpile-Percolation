import Sandpile.External.RSW.WiredArmConfiguration
import Sandpile.External.RSW.KSTPathInclusion

/-!
# Extending arms to wired crossings

An arm extends by one wired bond at each end to a vertical crossing between the
added boundary rows.
-/

open Percolation.Literature

namespace Sandpile.External.RSW

/-- An arm extends to a vertical crossing in the wired configuration. -/
theorem wired_crossing_of_kstArmEvent (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    (hω : ω ∈ kstArmEvent m) :
    ∃ (a b : centeredPlaneRectangle (m + m / 64) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 64) (m + 1))).Walk a b),
      (a : Site 2) 1 = (m : ℤ) + 1 ∧ (b : Site 2) 1 = -((m : ℤ) + 1) ∧
      IsBondOpenWalk (wiredArmConfig m ω) p := by
  classical
  let R := centeredPlaneRectangle (m + m / 64) m
  let S := centeredPlaneRectangle (m + m / 64) (m + 1)
  have hRS : R ⊆ S := by
    intro z hz
    have h := (mem_centeredPlaneRectangle _ _ z).mp hz
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    push_cast
    omega
  obtain ⟨a, b, p, ha, hb, hp⟩ := hω
  let f : rectangleGraph R →g rectangleGraph S := rectangleGraphInclusion hRS
  let top : Site 2 := (a : Site 2) + Pi.single 1 1
  let bottom : Site 2 := (b : Site 2) - Pi.single 1 1
  have ht0 : top 0 = (a : Site 2) 0 := by simp [top]
  have ht1 : top 1 = (m : ℤ) + 1 := by simp [top, ha.1]
  have hb0 : bottom 0 = (b : Site 2) 0 := by simp [bottom]
  have hb1 : bottom 1 = -((m : ℤ) + 1) := by simp [bottom, hb.1]; omega
  have htS : top ∈ S := by
    have h := (mem_centeredPlaneRectangle _ _ (a : Site 2)).mp a.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    rw [ht0, ht1]
    push_cast
    omega
  have hbS : bottom ∈ S := by
    have h := (mem_centeredPlaneRectangle _ _ (b : Site 2)).mp b.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    rw [hb0, hb1]
    push_cast
    omega
  let a' : S := ⟨top, htS⟩
  let b' : S := ⟨bottom, hbS⟩
  let aa : S := ⟨a, hRS a.property⟩
  let bb : S := ⟨b, hRS b.property⟩
  have htop : (rectangleGraph S).Adj a' aa := by
    have hh : (LatticeModels.zdGraph 2).Adj top (a : Site 2) := by
      have he : top - Pi.single (1 : Fin 2) (1 : ℤ) = (a : Site 2) := by
        simp [top]
      simpa only [he] using adj_sub_single_one top
    have hh' : (lattice 2).Adj top (a : Site 2) := by
      rw [lattice_eq_zdGraph]
      exact hh
    exact hh'
  have hbottom : (rectangleGraph S).Adj bb b' := by
    have hh : (LatticeModels.zdGraph 2).Adj (b : Site 2) bottom :=
      adj_sub_single_one (b : Site 2)
    have hh' : (lattice 2).Adj (b : Site 2) bottom := by
      rw [lattice_eq_zdGraph]
      exact hh
    exact hh'
  have hp' : IsBondOpenWalk (wiredArmConfig m ω) p := by
    apply (isBondOpenWalk_iff_local_edges _ p).mpr
    intro e he
    have hi : ∀ z ∈ Sym2.map Subtype.val e, -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m := by
      intro z hz
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact ((mem_centeredPlaneRectangle _ _ _).mp x.property).2.2
        · exact ((mem_centeredPlaneRectangle _ _ _).mp y.property).2.2
    rw [wiredArmConfig_eq_of_interior m ω _ hi]
    exact (isBondOpenWalk_iff_local_edges ω p).mp hp e he
  let q : (rectangleGraph S).Walk aa bb := p.map f
  have hpS : IsBondOpenWalk (wiredArmConfig m ω) q := hp'.map_inclusion hRS
  have htOpen : wiredArmConfig m ω s(top, (a : Site 2)) = true :=
    wiredArmConfig_upper_connector m ω top a ht1 ha.1 ha.2.1 ha.2.2
  have hbOpen : wiredArmConfig m ω s((b : Site 2), bottom) = true :=
    wiredArmConfig_lower_connector m ω b bottom hb1 hb.1 hb.2.1 hb.2.2
  refine ⟨a', b', (SimpleGraph.Walk.cons htop (q.append
    (SimpleGraph.Walk.cons hbottom SimpleGraph.Walk.nil))), ht1, hb1, ?_⟩
  exact ⟨htOpen, hpS.append ⟨hbOpen, trivial⟩⟩

/-- The arm event is equivalent to a crossing of its wired rectangle. -/
theorem kstArmEvent_iff_canonical_wired_crossing (m : ℕ) (hm : 0 < m)
    (ω : Sym2 (Site 2) → Bool) :
    ω ∈ kstArmEvent m ↔
      ∃ (a b : centeredPlaneRectangle (m + m / 64) (m + 1))
        (p : (rectangleGraph (centeredPlaneRectangle (m + m / 64) (m + 1))).Walk a b),
        (a : Site 2) 1 = (m : ℤ) + 1 ∧ (b : Site 2) 1 = -((m : ℤ) + 1) ∧
        IsBondOpenWalk (wiredArmConfig m ω) p :=
  ⟨wired_crossing_of_kstArmEvent m ω, kstArmEvent_of_canonical_wired_crossing m hm ω⟩

end Sandpile.External.RSW
