import Sandpile.External.RSW.ArcIntersection
import Sandpile.External.RSW.QuasiClosing
import Sandpile.External.RSW.QuasiCascadeProbability

/-!
# Bridge and path intersection

A bridge joins the outer boundary arcs of the scale rectangle, while a KST path joins
its central top and bottom targets. These alternating boundary paths intersect.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Every positive-scale KST path intersects every bridge at the same scale. -/
theorem kstBridgeIntersectsPaths (n m : ℕ) (hm : 0 < m) : KSTBridgeIntersectsPaths n m := by
  let Q := centeredPlaneRectangle (n + 3 * (n / 12)) n
  let R := centeredPlaneRectangle (m + m / 12) m
  intro a b p c d r hp hc hd
  rcases hp with ⟨_, ha, hb, haL, haR, hbL, hbR, hpQ⟩
  let fq : rectangleGraph Q →g LatticeModels.zdGraph 2 := ⟨Subtype.val, fun h => by
    rw [← lattice_eq_zdGraph]
    exact h⟩
  let fr : rectangleGraph R →g LatticeModels.zdGraph 2 := ⟨Subtype.val, fun h => by
    rw [← lattice_eq_zdGraph]
    exact h⟩
  have hpbox : ∀ z ∈ (p.map fq).support,
      -((m + m / 12 : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
        -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp (hpQ z' hz')
  have hrbox : ∀ z ∈ (r.map fr).support,
      -((m + m / 12 : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
        -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp z'.property
  have hL : -((m + m / 12 : ℕ) : ℤ) < -((m / 12 : ℕ) : ℤ) := by
    push_cast
    omega
  have hR : ((m / 12 : ℕ) : ℤ) < ((m + m / 12 : ℕ) : ℤ) := by
    push_cast
    omega
  have hBT : -(m : ℤ) < m := by omega
  obtain ⟨z, hz₁, hz₂⟩ := alternating_boundary_paths_intersect hL hR hBT
    (p.map fq) (r.map fr) hpbox hrbox ⟨ha, haL, haR⟩ ⟨hb, hbL, hbR⟩ hc hd
  rw [SimpleGraph.Walk.support_map] at hz₁ hz₂
  obtain ⟨z₁, hz₁, he₁⟩ := List.mem_map.mp hz₁
  obtain ⟨z₂, hz₂, he₂⟩ := List.mem_map.mp hz₂
  refine ⟨z₁, hz₁, List.mem_map.mpr ⟨z₂, hz₂, ?_⟩⟩
  change (z₂ : Site 2) = (z₁ : Site 2)
  exact he₂.trans he₁.symm

/-- A bridge closes every positive-scale quasi-crossing. -/
theorem kstQuasiClosing (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    kstQuasiCrossingEvent n m ∩ kstBridgeEvent m ⊆ kstBridgeEvent n :=
  kstQuasiClosing_of_bridge_intersects n m hmn (kstBridgeIntersectsPaths n m hm)

/-- The quasi-crossing closing probability estimate for an associated bond law. -/
theorem measureReal_kstQuasiCrossing_mul_bridge_le
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    μ.real (kstQuasiCrossingEvent n m) * μ.real (kstBridgeEvent m) ≤
      μ.real (kstBridgeEvent n) :=
  kstQuasiClosing_probability μ ha n m (kstQuasiClosing n m hm hmn)

end Sandpile.External.RSW
