import Sandpile.External.RSW.ArmBridge
import Sandpile.External.RSW.BondWalk
import Sandpile.External.RSW.BridgeBound
import Sandpile.External.RSW.CenteredMonotonicity

/-!
# Closing a quasi-crossing

If each scale-`m` path intersects the bridge inside its scale rectangle, the bridge
joins the two walls of a quasi-crossing. Their concatenation yields a bridge at the
larger scale.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- The geometric intersection condition needed to close a quasi-crossing. -/
def KSTBridgeIntersectsPaths (n m : ℕ) : Prop :=
  let Q := centeredPlaneRectangle (n + 3 * (n / 12)) n
  let R := centeredPlaneRectangle (m + m / 12) m
  ∀ (a b : Q) (p : (rectangleGraph Q).Walk a b)
    (c d : R) (r : (rectangleGraph R).Walk c d),
    IsKSTPath m p → kstBridgeLeft m c → kstBridgeRight m d →
    ∃ x : Q, x ∈ p.support ∧ (x : Site 2) ∈ r.support.map Subtype.val

/-- The bridge intersection property gives the deterministic quasi-crossing closing
inclusion. -/
theorem kstQuasiClosing_of_bridge_intersects (n m : ℕ) (hmn : m ≤ n)
    (hint : KSTBridgeIntersectsPaths n m) :
    kstQuasiCrossingEvent n m ∩ kstBridgeEvent m ⊆ kstBridgeEvent n := by
  let Q := centeredPlaneRectangle (n + 3 * (n / 12)) n
  let R := centeredPlaneRectangle (m + m / 12) m
  have hdiv : m / 12 ≤ n / 12 := Nat.div_le_div_right hmn
  have hRQ : R ⊆ Q := by
    intro z hz
    have hz' := (mem_centeredPlaneRectangle _ _ z).mp hz
    apply (mem_centeredPlaneRectangle _ _ z).mpr
    have hdiv' : ((m / 12 : ℕ) : ℤ) ≤ (n / 12 : ℕ) := by exact_mod_cast hdiv
    have hmn' : (m : ℤ) ≤ n := by exact_mod_cast hmn
    push_cast at *
    omega
  let f : rectangleGraph R →g rectangleGraph Q :=
    ⟨fun z => ⟨z.val, hRQ z.property⟩, fun h => h⟩
  intro ω hω
  obtain ⟨hleft, hright⟩ := hω.1
  obtain ⟨a₁, b₁, x₁, c₁, p₁, q₁, hp₁, hx₁, hc₁, hpo₁, hqo₁⟩ := hleft
  obtain ⟨a₂, b₂, x₂, c₂, p₂, q₂, hp₂, hx₂, hc₂, hpo₂, hqo₂⟩ := hright
  obtain ⟨u, v, r, hu, hv, hro⟩ := hω.2
  obtain ⟨z₁, hz₁, hz₁r⟩ := hint a₁ b₁ p₁ u v r hp₁ hu hv
  obtain ⟨z₂, hz₂, hz₂r⟩ := hint a₂ b₂ p₂ u v r hp₂ hu hv
  have hmem (z : Q) (hz : (z : Site 2) ∈ r.support.map Subtype.val) :
      z ∈ (r.map f).support := by
    rw [SimpleGraph.Walk.support_map]
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hz
    refine List.mem_map.mpr ⟨y, hy, ?_⟩
    apply Subtype.ext
    exact he
  have hr₀ : IsBondOpenWalk ω (r.map f) := by
    apply (isBondOpenWalk_map id f (fun _ => rfl) ω r).mpr
    simpa only [Sym2.map_id, Function.comp_id] using hro
  obtain ⟨s₁, hs₁, _⟩ := exists_openWalk_of_mem_support p₁ hpo₁ hx₁ hz₁
  obtain ⟨s₂, hs₂, _⟩ := exists_openWalk_of_mem_support p₂ hpo₂ hz₂ hx₂
  obtain ⟨s, hs, _⟩ := exists_openWalk_of_mem_support (r.map f) hr₀
    (hmem z₁ hz₁r) (hmem z₂ hz₂r)
  have hwide : ω ∈ centeredBondCrossingEvent (n + 3 * (n / 12)) n := by
    apply (mem_centeredBondCrossingEvent_iff _ _ _).mpr
    refine ⟨c₁, c₂, ((q₁.reverse.append s₁).append s).append (s₂.append q₂), hc₁, hc₂, ?_⟩
    exact ((hqo₁.reverse.append hs₁).append hs).append (hs₂.append hqo₂)
  have hsmall : ω ∈ centeredBondCrossingEvent (n + n / 12) n :=
    centeredBondCrossingEvent_anti_width (by omega) hwide
  exact centeredBondCrossingEvent_subset_kstBridgeEvent n hsmall

end Sandpile.External.RSW
