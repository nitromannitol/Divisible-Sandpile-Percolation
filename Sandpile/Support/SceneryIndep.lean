import Mathlib
import Sandpile.Law
import Sandpile.Support.BallCrossingDefinitions

open MeasureTheory ProbabilityTheory LatticeProb

set_option maxHeartbeats 1000000

namespace Sandpile

/-- Pullback of independence along a measure-preserving map. -/
theorem indep_comap_fst_snd_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ₁ : Measure α) (ρ₂ : Measure β) [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂] :
    Indep (MeasurableSpace.comap Prod.fst inferInstance)
          (MeasurableSpace.comap Prod.snd inferInstance) (ρ₁.prod ρ₂) :=
  IndepFun_iff_Indep Prod.fst Prod.snd (ρ₁.prod ρ₂) |>.1
    (indepFun_prod (measurable_id) (measurable_id))

theorem indep_comap_prod_fst_snd {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure Ω} {ρ₁ : Measure α} {ρ₂ : Measure β}
    (Φ : Ω → α × β) (hΦ : MeasurePreserving Φ μ (ρ₁.prod ρ₂))
    [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂] :
    Indep (MeasurableSpace.comap (Prod.fst ∘ Φ) inferInstance)
          (MeasurableSpace.comap (Prod.snd ∘ Φ) inferInstance) μ := by
  rw [Indep_iff]
  intro t1 t2 ht1 ht2
  rw [MeasurableSpace.measurableSet_comap] at ht1 ht2
  obtain ⟨A, hA, rfl⟩ := ht1
  obtain ⟨B, hB, rfl⟩ := ht2
  have hA' : MeasurableSet A := hA
  have hB' : MeasurableSet B := hB
  have h1 : μ ((Prod.fst ∘ Φ) ⁻¹' A) = ρ₁ A := by
    have : (Prod.fst ∘ Φ) ⁻¹' A = Φ ⁻¹' (Prod.fst ⁻¹' A) := rfl
    rw [this, hΦ.measure_preimage (measurable_fst hA |>.nullMeasurableSet)]
    exact measurePreserving_fst.measure_preimage hA.nullMeasurableSet
  have h2 : μ ((Prod.snd ∘ Φ) ⁻¹' B) = ρ₂ B := by
    have : (Prod.snd ∘ Φ) ⁻¹' B = Φ ⁻¹' (Prod.snd ⁻¹' B) := rfl
    rw [this, hΦ.measure_preimage (measurable_snd hB |>.nullMeasurableSet)]
    exact measurePreserving_snd.measure_preimage hB.nullMeasurableSet
  have h3 : μ ((Prod.fst ∘ Φ) ⁻¹' A ∩ (Prod.snd ∘ Φ) ⁻¹' B) = ρ₁ A * ρ₂ B := by
    have hpre : (Prod.fst ∘ Φ) ⁻¹' A ∩ (Prod.snd ∘ Φ) ⁻¹' B
        = Φ ⁻¹' (A ×ˢ B) := by
      ext ω; simp [Set.mem_preimage]
    rw [hpre, hΦ.measure_preimage (hA.prod hB |>.nullMeasurableSet)]
    exact Measure.prod_prod A B
  rw [h3, h1, h2]

/-- Coordinate-block independence under the i.i.d. scenery law: the
sigma-algebras read through two disjoint finite site sets are independent. -/
theorem indep_comap_pi_disjoint (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (U V : Finset (Site 2)) (hUV : Disjoint (U : Set (Site 2)) (V : Set (Site 2))) :
    Indep (MeasurableSpace.comap (fun ω : Site 2 → ℝ => fun k : {x // x ∈ U} => ω k.val)
            (inferInstance : MeasurableSpace (({x // x ∈ U} : Type) → ℝ)))
          (MeasurableSpace.comap (fun ω : Site 2 → ℝ => fun k : {x // x ∈ V} => ω k.val)
            (inferInstance : MeasurableSpace (({x // x ∈ V} : Type) → ℝ)))
          (LatticeProb.iidLaw 2 ν) := by
  set W := U ∪ V
  -- the projection through W
  set πW : (Site 2 → ℝ) → ({x // x ∈ W} → ℝ) := fun ω k => ω k.val with hπW
  -- its law is the finite product
  have hW : MeasurePreserving πW (LatticeProb.iidLaw 2 ν)
      (Measure.pi (fun _ : {x // x ∈ W} => ν)) := by
    refine ⟨?_, ?_⟩
    · exact measurable_pi_lambda _ fun k => measurable_pi_apply k.val
    · show (LatticeProb.iidLaw 2 ν).map πW = _
      rw [show LatticeProb.iidLaw 2 ν = Measure.infinitePi (fun _ : Site 2 => ν) from rfl]
      rw [Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]
      rw [Measure.infinitePi_eq_pi]
  -- the subtype-splitting equivalence on the W-product
  set p : {x // x ∈ W} → Prop := fun i => (i : Site 2) ∈ U with hp
  set E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {x // x ∈ W} => ℝ) p with hE
  -- independence of the two components after the split
  have hcomp := indep_comap_fst_snd_prod
    (Measure.pi (fun _ : {i : {x // x ∈ W} // p i} => ν))
    (Measure.pi (fun _ : {i : {x // x ∈ W} // ¬p i} => ν))
  -- the composite is measure-preserving into the split product
  have hE : MeasurePreserving (fun ω => E (πW ω)) (LatticeProb.iidLaw 2 ν)
      ((Measure.pi (fun _ : {i : {x // x ∈ W} // p i} => ν)).prod
        (Measure.pi (fun _ : {i : {x // x ∈ W} // ¬p i} => ν))) :=
    (measurePreserving_piEquivPiSubtypeProd (fun _ : {x // x ∈ W} => ν) p).comp hW
  -- pull back the component independence
  have hpull := indep_comap_prod_fst_snd _ hE
  -- the U-coordinate projection factors through the first block
  have hcU : Measurable
      (fun ρ : {i : {x // x ∈ W} // p i} → ℝ =>
        fun k : {x // x ∈ U} => ρ ⟨⟨k.val, Finset.mem_union_left V k.2⟩, k.2⟩) :=
    measurable_pi_lambda _
      (fun k : {x // x ∈ U} => measurable_pi_apply _)
  have hcV : Measurable
      (fun ρ : {i : {x // x ∈ W} // ¬p i} → ℝ =>
        fun k : {x // x ∈ V} =>
          ρ ⟨⟨k.val, Finset.mem_union_right U k.2⟩,
            fun hU => by
              have h2 : (k : Site 2) ∈ (U : Set (Site 2)) ∩ (V : Set (Site 2)) :=
                ⟨hU, Finset.mem_coe.2 k.2⟩
              rw [hUV.inter_eq] at h2
              exact h2⟩) :=
    measurable_pi_lambda _
      (fun k : {x // x ∈ V} => measurable_pi_apply _)
  have hle1 : MeasurableSpace.comap (fun ω : Site 2 → ℝ => fun k : {x // x ∈ U} => ω k.val)
      (inferInstance : MeasurableSpace (({x // x ∈ U} : Type) → ℝ))
      ≤ MeasurableSpace.comap (fun ω : Site 2 → ℝ => Prod.fst (E (πW ω)))
          (inferInstance : MeasurableSpace (({i : {x // x ∈ W} // p i} : Type) → ℝ)) := by
    have h1 : (fun ω : Site 2 → ℝ => fun k : {x // x ∈ U} => ω k.val)
        = (fun ρ : {i : {x // x ∈ W} // p i} → ℝ =>
            fun k : {x // x ∈ U} => ρ ⟨⟨k.val, Finset.mem_union_left V k.2⟩, k.2⟩)
          ∘ (fun ω : Site 2 → ℝ => Prod.fst (E (πW ω))) := rfl
    rw [h1, ← MeasurableSpace.comap_comp]
    have hinner : MeasurableSpace.comap
        (fun ρ : {i : {x // x ∈ W} // p i} → ℝ =>
          fun k : {x // x ∈ U} => ρ ⟨⟨k.val, Finset.mem_union_left V k.2⟩, k.2⟩)
        (inferInstance : MeasurableSpace (({x // x ∈ U} : Type) → ℝ))
        ≤ (inferInstance : MeasurableSpace (({i : {x // x ∈ W} // p i} : Type) → ℝ)) :=
      measurable_iff_comap_le.mp hcU
    exact MeasurableSpace.comap_mono hinner
  have hle2 : MeasurableSpace.comap (fun ω : Site 2 → ℝ => fun k : {x // x ∈ V} => ω k.val)
      (inferInstance : MeasurableSpace (({x // x ∈ V} : Type) → ℝ))
      ≤ MeasurableSpace.comap (fun ω : Site 2 → ℝ => Prod.snd (E (πW ω)))
          (inferInstance : MeasurableSpace (({i : {x // x ∈ W} // ¬p i} : Type) → ℝ)) := by
    have h2 : (fun ω : Site 2 → ℝ => fun k : {x // x ∈ V} => ω k.val)
        = (fun ρ : {i : {x // x ∈ W} // ¬p i} → ℝ =>
            fun k : {x // x ∈ V} =>
              ρ ⟨⟨k.val, Finset.mem_union_right U k.2⟩,
                fun hU => by
                  have h3 : (k : Site 2) ∈ (U : Set (Site 2)) ∩ (V : Set (Site 2)) :=
                    ⟨hU, Finset.mem_coe.2 k.2⟩
                  rw [hUV.inter_eq] at h3
                  exact h3⟩)
          ∘ (fun ω : Site 2 → ℝ => Prod.snd (E (πW ω))) := by
      funext ω k
      rfl
    rw [h2, ← MeasurableSpace.comap_comp]
    have hinner : MeasurableSpace.comap
        (fun ρ : {i : {x // x ∈ W} // ¬p i} → ℝ =>
          fun k : {x // x ∈ V} =>
            ρ ⟨⟨k.val, Finset.mem_union_right U k.2⟩,
              fun hU => by
                have h3 : (k : Site 2) ∈ (U : Set (Site 2)) ∩ (V : Set (Site 2)) :=
                  ⟨hU, Finset.mem_coe.2 k.2⟩
                rw [hUV.inter_eq] at h3
                exact h3⟩)
        (inferInstance : MeasurableSpace (({x // x ∈ V} : Type) → ℝ))
        ≤ (inferInstance : MeasurableSpace (({i : {x // x ∈ W} // ¬p i} : Type) → ℝ)) :=
      measurable_iff_comap_le.mp hcV
    exact MeasurableSpace.comap_mono hinner
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hpull hle1) hle2
end Sandpile
