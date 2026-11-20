import Sandpile.External.RSW.WiredDualTransfer
import Sandpile.External.RSW.ArmDualObstruction

/-!
# Dual bridge obstruction for an absent arm

An absent arm forces an open bridge in the original dual configuration.
-/

open Set

namespace Sandpile.External.RSW

/-- If the arm is absent, the dual configuration has a bridge with the same offset. -/
theorem dual_centeredBridge_of_not_kstArmEvent (m : ℕ) (hm : 64 ≤ m)
    (ω : Sym2 (Site 2) → Bool) (h : ω ∉ kstArmEvent m) :
    dualBondConfig ω ∈ centeredBridgeEvent m (m / 64) := by
  obtain ⟨a, b, p, hp, ha, hb, htop, hs⟩ :=
    exists_wired_dual_clipped_path_of_not_kstArmEvent m hm ω h
  have hstrip : ∀ z ∈ p.support, -(m : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m := by
    intro z hz
    have hz' := (mem_centeredPlaneRectangle _ _ _).mp (hs z hz)
    exact hz'.2.2
  have hopen := hp.of_wired_dual_strip m ω p hstrip htop
  let Q := centeredPlaneRectangle (m + m / 64 + 1) (m + 1)
  let R := centeredPlaneRectangle (m + m / 64) m
  change ((lattice 2).induce (Q : Set (Site 2))).Walk a b at p
  let P := p.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom
  have hP : ∀ z ∈ P.support, z ∈ (R : Set (Site 2)) := by
    intro z hz
    change z ∈ (p.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact hs x hx
  let q := P.induce (R : Set (Site 2)) hP
  have hq : q.map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom = P :=
    SimpleGraph.Walk.map_induce P hP
  change bondConnectionEvent R _ _ (dualBondConfig ω)
  refine ⟨⟨a, hP _ P.start_mem_support⟩, ⟨b, hP _ P.end_mem_support⟩, q, ha, hb, ?_⟩
  apply (isBondOpenWalk_iff_edges (dualBondConfig ω) q).mpr
  intro e he
  rw [hq] at he
  exact (isBondOpenWalk_iff_edges (dualBondConfig ω) p).mp hopen e he

/-- The dual bridge probability bounds the complement of the arm probability. -/
theorem one_sub_dual_centeredBridge_le_arm
    (μ : MeasureTheory.Measure (Sym2 (Site 2) → Bool)) [MeasureTheory.IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasureTheory.MeasurePreserving
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (m : ℕ) (hm : 64 ≤ m) :
    1 - (μ.map dualBondConfig).real (centeredBridgeEvent m (m / 64)) ≤
      μ.real (kstArmEvent m) := by
  apply one_sub_dualBridge_le_arm_of_subset μ ht m 0
  intro ω hω
  simp only [Set.mem_preimage, add_zero]
  change (dualBondConfig ω ∘ Sym2.map id) ∈ centeredBridgeEvent m (m / 64)
  rw [Sym2.map_id, Function.comp_id]
  exact dual_centeredBridge_of_not_kstArmEvent m hm ω hω

/-- The six-event inclusion and corridor cover imply planar RSW. -/
theorem planarRSW_of_six_event_and_corridor
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcover : ∀ i j, j < i → KSTCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_dual_bridge_obstruction_and_geometry ?_ hgeom hcover
  intro μ _ hμ s hs hdiv
  have h64 : 64 ∣ s := dvd_trans (by norm_num : 64 ∣ 192) hdiv
  have hlarge : 64 ≤ s := Nat.le_of_dvd hs h64
  exact one_sub_dual_centeredBridge_le_arm μ hμ.2.1 s hlarge

end Sandpile.External.RSW
