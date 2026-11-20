import Sandpile.External.RSW.ArmBridge
import Sandpile.External.RSW.EdgeSymmetry
import Sandpile.External.RSW.BondWalk
import Sandpile.External.RSW.AspectGluing
import Sandpile.External.RSW.BaseScaleArithmetic

/-!
# Rectangle crossings from arms

An arm rotated by a quarter turn is a horizontal rectangle crossing. At the intermediate
scale of the four-arm construction, this crossing fits the two auxiliary rectangles.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- An arm gives a centered horizontal crossing after swapping coordinates. -/
theorem kstArmEvent_subset_swap_centeredCrossing (m : ℕ) :
    kstArmEvent m ⊆
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite) ⁻¹'
        centeredBondCrossingEvent m (m + m / 64) := by
  let Q := centeredPlaneRectangle (m + m / 64) m
  let R := centeredPlaneRectangle m (m + m / 64)
  have hQR (z : Q) : swapPlaneSite z ∈ R := by
    have hz := (mem_centeredPlaneRectangle _ _ z).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    simpa only [swapPlaneSite, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using ⟨hz.2.2.1, hz.2.2.2, hz.1, hz.2.1⟩
  let f : rectangleGraph Q →g rectangleGraph R :=
    ⟨fun z => ⟨swapPlaneSite z, hQR z⟩, fun h => lattice_adj_swap_plane h⟩
  intro ω hω
  obtain ⟨a, b, p, ha, hb, hp⟩ := hω
  apply (mem_centeredBondCrossingEvent_iff m (m + m / 64) _).mpr
  refine ⟨f b, f a, (p.map f).reverse, ?_, ?_, ?_⟩
  · change (b : Site 2) 1 = -(m : ℤ)
    exact hb.1
  · change (a : Site 2) 1 = (m : ℤ)
    exact ha.1
  · apply IsBondOpenWalk.reverse
    apply (isBondOpenWalk_map swapPlaneSite f (fun _ => rfl) _ p).mpr
    have he : (ω ∘ Sym2.map swapPlaneSite) ∘ Sym2.map swapPlaneSite = ω := by
      funext e
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Function.comp_apply, Sym2.map_mk]
        rw [swapPlaneSite_involutive x, swapPlaneSite_involutive y]
    rw [he]
    exact hp

/-- A symmetric, translation-invariant bond law assigns an arm no more probability than
the corresponding rotated rectangle crossing. -/
theorem measureReal_kstArm_le_rotated_crossing (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (m : ℕ) :
    μ.real (kstArmEvent m) ≤ μ.real (bondCrossingEvent (2 * m) (2 * (m + m / 64))) := by
  have hcenter : μ.real (centeredBondCrossingEvent m (m + m / 64)) =
      μ.real (bondCrossingEvent (2 * m) (2 * (m + m / 64))) :=
    (ht (- ![(m : ℤ), ((m + m / 64 : ℕ) : ℤ)])).measureReal_preimage
      (measurableSet_bondCrossingEvent _ _).nullMeasurableSet
  exact (measureReal_mono (kstArmEvent_subset_swap_centeredCrossing m) (measure_ne_top μ _)).trans
    ((hs.measureReal_preimage (measurableSet_centeredBondCrossingEvent _ _).nullMeasurableSet).le.trans
      hcenter.le)

/-- The intermediate arm is bounded by either of the horizontal rectangle crossings used
in the adjacent-scale construction. -/
theorem measureReal_kstArm_intermediate_le_crossing (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (j : ℕ) :
    μ.real (kstArmEvent (31 * kstBaseScale j / 8)) ≤
      μ.real (bondCrossingEvent (8 * kstBaseScale j - 3 * (kstBaseScale j / 12))
        (8 * kstBaseScale j)) := by
  have hscale := (kstBaseScale_intermediate j).2.2
  have hoff := (kstBaseScale_intermediate_offsets j).2.2.1
  have hβ := (kstBaseScale_offsets j).2
  have hwidth : 8 * kstBaseScale j - 3 * (kstBaseScale j / 12) ≤
      2 * (31 * kstBaseScale j / 8) := by
    rw [hβ, hscale]
    dsimp only [kstBaseScale]
    omega
  have hheight : 2 * (31 * kstBaseScale j / 8 + (31 * kstBaseScale j / 8) / 64) ≤
      8 * kstBaseScale j := by
    rw [hoff, hscale]
    dsimp only [kstBaseScale]
    omega
  exact (measureReal_kstArm_le_rotated_crossing μ ht hs _).trans
    (measureReal_mono (bondCrossingEvent_width_height_mono hwidth hheight) (measure_ne_top μ _))

end Sandpile.External.RSW
