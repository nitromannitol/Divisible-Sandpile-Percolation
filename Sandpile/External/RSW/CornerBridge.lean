import Sandpile.External.RSW.CornerIntersection
import Sandpile.External.RSW.BridgePieceSymmetry

/-!
# Joining corner connections

A lower right-corner connection and its horizontal reflection together produce a
connection between the two lower boundary segments.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A connection between the two lower boundary segments of the bridge rectangle. -/
def kstBottomBridgeEvent (m : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  bondConnectionEvent (centeredPlaneRectangle (m + m / 12) m)
    {z | kstBridgeCorner m true false z} {z | kstBridgeCorner m false false z}

/-- The bottom bridge event is increasing. -/
theorem isUpperSet_kstBottomBridgeEvent (m : ℕ) : IsUpperSet (kstBottomBridgeEvent m) :=
  isUpperSet_bondConnectionEvent _ _ _

/-- The bottom bridge event is measurable. -/
theorem measurableSet_kstBottomBridgeEvent (m : ℕ) : MeasurableSet (kstBottomBridgeEvent m) :=
  measurableSet_bondConnectionEvent _ _ _

/-- Opposite reflected corner connections give a bottom bridge. -/
theorem kstBridgePiece_one_inter_reflect_subset_bottom (m : ℕ) (hm : 12 ≤ m) :
    kstBridgePieceEvent m 1 ∩
      (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (reflectPlaneCoordinates true false)) ⁻¹' kstBridgePieceEvent m 1 ⊆
      kstBottomBridgeEvent m := by
  intro ω hω
  let Q := centeredPlaneRectangle (m + m / 12) m
  let f := reflectBridgeRectangle m true false
  obtain ⟨a, b, p, ha, hb, hp⟩ := hω.1
  obtain ⟨a', b', p', ha', hb', hp'⟩ := hω.2
  let c := f b'
  let d := f a'
  let q := (p'.map f).reverse
  have hq : IsBondOpenWalk ω q := by
    apply IsBondOpenWalk.reverse
    exact (isBondOpenWalk_map (reflectPlaneCoordinates true false) f (fun _ => rfl) ω p').mpr hp'
  have hc : kstBridgeCorner m true false c := by
    change kstBridgeCorner m false false b' at hb'
    change kstBridgeCorner m true false (reflectBridgeRectangle m true false b')
    simp [kstBridgeCorner, reflectBridgeRectangle_apply, reflectPlaneCoordinates] at hb' ⊢
    omega
  have hd : kstBridgeRight m d := by
    change kstBridgeLeft m a' at ha'
    change kstBridgeRight m (reflectBridgeRectangle m true false a')
    simp [kstBridgeLeft, kstBridgeRight, reflectBridgeRectangle_apply, reflectPlaneCoordinates] at ha' ⊢
    omega
  change kstBridgeLeft m a at ha
  change kstBridgeCorner m false false b at hb
  by_cases haBottom : (a : Site 2) 1 = -(m : ℤ)
  · have haCorner : kstBridgeCorner m true false a := by
      have haBox := (mem_centeredPlaneRectangle _ _ a).mp a.property
      simp only [kstBridgeCorner, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
      rcases ha with ha | ⟨ha, _⟩
      · push_cast at ha
        constructor <;> omega
      · exact ⟨ha, haBottom⟩
    exact ⟨a, b, p, haCorner, hb, hp⟩
  by_cases hdBottom : (d : Site 2) 1 = -(m : ℤ)
  · have hdCorner : kstBridgeCorner m false false d := by
      simp only [kstBridgeCorner, Bool.false_eq_true, ↓reduceIte]
      rcases hd with hd | ⟨hd, _⟩
      · push_cast at hd
        constructor <;> omega
      · exact ⟨hd, hdBottom⟩
    exact ⟨c, d, q, hc, hdCorner, hq⟩
  have hbetaNat : 0 < m / 12 := Nat.div_pos hm (by omega)
  have hbeta : (0 : ℤ) < ((m / 12 : ℕ) : ℤ) := by exact_mod_cast hbetaNat
  let g : rectangleGraph Q →g LatticeModels.zdGraph 2 := ⟨Subtype.val, fun h => by
    rw [← lattice_eq_zdGraph]
    exact h⟩
  have hpbox : ∀ z ∈ (p.map g).support,
      -((m + m / 12 : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
        -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp z'.property
  have hqbox : ∀ z ∈ (q.map g).support,
      -((m + m / 12 : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
        -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp z'.property
  have haBox := (mem_centeredPlaneRectangle _ _ a).mp a.property
  have hdBox := (mem_centeredPlaneRectangle _ _ d).mp d.property
  have ha'': ((a : Site 2) 0 = -((m + m / 12 : ℕ) : ℤ) ∨
      ((a : Site 2) 1 = m ∧ (a : Site 2) 0 < 0)) ∧ -(m : ℤ) < (a : Site 2) 1 := by
    rcases ha with ha | ⟨ha, haB | haT⟩
    · exact ⟨Or.inl ha, by omega⟩
    · exact (haBottom haB).elim
    · exact ⟨Or.inr ⟨haT, by omega⟩, by omega⟩
  have hb'' : (b : Site 2) 1 = -(m : ℤ) ∧ 0 < (b : Site 2) 0 := by
    have hh := hb
    simp only [kstBridgeCorner, Bool.false_eq_true, ↓reduceIte] at hh
    exact ⟨hh.2, by omega⟩
  have hc'' : (c : Site 2) 1 = -(m : ℤ) ∧ (c : Site 2) 0 < 0 := by
    have hh := hc
    simp only [kstBridgeCorner, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte] at hh
    exact ⟨hh.2, by omega⟩
  have hd'' : ((d : Site 2) 0 = ((m + m / 12 : ℕ) : ℤ) ∨
      ((d : Site 2) 1 = m ∧ 0 < (d : Site 2) 0)) ∧ -(m : ℤ) < (d : Site 2) 1 := by
    rcases hd with hd | ⟨hd, hdB | hdT⟩
    · exact ⟨Or.inl hd, by omega⟩
    · exact (hdBottom hdB).elim
    · exact ⟨Or.inr ⟨hdT, by omega⟩, by omega⟩
  obtain ⟨z, hzp, hzq⟩ := corner_boundary_paths_intersect
    (show -((m + m / 12 : ℕ) : ℤ) < 0 by push_cast; omega)
    (show 0 < ((m + m / 12 : ℕ) : ℤ) by push_cast; omega)
    (show -(m : ℤ) < m by omega) (p.map g) (q.map g) hpbox hqbox ha'' hb'' hc'' hd''
  rw [SimpleGraph.Walk.support_map] at hzp hzq
  obtain ⟨x, hxp, hxe⟩ := List.mem_map.mp hzp
  obtain ⟨y, hyq, hye⟩ := List.mem_map.mp hzq
  have hxy : x = y := Subtype.ext (hxe.trans hye.symm)
  subst y
  obtain ⟨q₀, hq₀, _⟩ := exists_openWalk_of_mem_support q hq q.start_mem_support hyq
  obtain ⟨p₀, hp₀, _⟩ := exists_openWalk_of_mem_support p hp hxp p.end_mem_support
  exact ⟨c, b, q₀.append p₀, hc, hb, hq₀.append hp₀⟩

/-- Positive association bounds the bottom bridge probability by the square of the
corner-piece probability. -/
theorem measureReal_kstBridgePiece_one_sq_le_bottom (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ) (m : ℕ) (hm : 12 ≤ m) :
    μ.real (kstBridgePieceEvent m 1) ^ 2 ≤ μ.real (kstBottomBridgeEvent m) := by
  let A := kstBridgePieceEvent m 1
  let f : (Sym2 (Site 2) → Bool) → (Sym2 (Site 2) → Bool) :=
    fun ω => ω ∘ Sym2.map (reflectPlaneCoordinates true false)
  have hf := measurePreserving_reflectPlaneCoordinates μ hs hr true false
  have hupper : IsUpperSet (f ⁻¹' A) := by
    intro ω η hω h
    exact isUpperSet_kstBridgePieceEvent m 1 (fun e => hω _) h
  have hmeas : MeasurableSet (f ⁻¹' A) := (measurableSet_kstBridgePieceEvent m 1).preimage hf.measurable
  have hp : μ.real (f ⁻¹' A) = μ.real A :=
    hf.measureReal_preimage (measurableSet_kstBridgePieceEvent m 1).nullMeasurableSet
  have hh := ha A (f ⁻¹' A) (isUpperSet_kstBridgePieceEvent m 1) hupper
    (measurableSet_kstBridgePieceEvent m 1) hmeas
  rw [hp] at hh
  calc
    μ.real A ^ 2 = μ.real A * μ.real A := sq _
    _ ≤ μ.real (A ∩ f ⁻¹' A) := hh
    _ ≤ μ.real (kstBottomBridgeEvent m) :=
      measureReal_mono (kstBridgePiece_one_inter_reflect_subset_bottom m hm) (measure_ne_top μ _)

end Sandpile.External.RSW
