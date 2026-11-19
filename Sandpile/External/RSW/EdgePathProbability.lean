import Sandpile.External.RSW.BridgeBound

/-!
# Straight open paths

Under positive association and translation invariance, the probability of an open straight
horizontal path is at least the corresponding power of the one-edge probability.
-/

open LatticeProb MeasureTheory Set Percolation.Literature
open scoped BigOperators

namespace Sandpile.External.RSW

/-- The event that one bond is open. -/
def bondOpenEvent (e : Sym2 (Site 2)) : Set (Sym2 (Site 2) → Bool) :=
  {ω | ω e = true}

/-- A one-bond open event is increasing. -/
theorem isUpperSet_bondOpenEvent (e : Sym2 (Site 2)) : IsUpperSet (bondOpenEvent e) := by
  intro ω η hω h
  have hh := hω e
  change ω e = true at h
  rw [h] at hh
  exact le_antisymm le_top hh

/-- A one-bond open event is measurable. -/
theorem measurableSet_bondOpenEvent (e : Sym2 (Site 2)) : MeasurableSet (bondOpenEvent e) :=
  (measurableSet_singleton true).preimage (measurable_pi_apply e)

/-- The `i`th bond in the horizontal row starting at the origin. -/
def horizontalBond (i : ℕ) : Sym2 (Site 2) := s(pt i 0, pt (i + 1) 0)

/-- Row bonds are translates of the first row bond. -/
theorem horizontalBond_eq_translate (i : ℕ) :
    horizontalBond i = Sym2.map (fun z => z + pt i 0) (horizontalBond 0) := by
  have h₀ : pt (0 : ℤ) 0 + pt i 0 = pt i 0 := by
    ext j
    fin_cases j <;> simp [pt]
  have h₁ : pt (1 : ℤ) 0 + pt i 0 = pt (i + 1) 0 := by
    ext j
    fin_cases j <;> simp [pt, add_comm]
  simp only [horizontalBond, Sym2.map_mk, h₀, h₁, Nat.cast_zero, zero_add]

/-- Translation-invariant laws have the same open probability for every bond in the row. -/
theorem measureReal_horizontalBond_eq (μ : Measure (Sym2 (Site 2) → Bool))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ) (i : ℕ) :
    μ.real (bondOpenEvent (horizontalBond i)) = μ.real (bondOpenEvent (horizontalBond 0)) := by
  have he : (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + pt i 0)) ⁻¹'
      bondOpenEvent (horizontalBond 0) = bondOpenEvent (horizontalBond i) := by
    ext ω
    simp only [bondOpenEvent, mem_preimage, mem_ofPred_eq, Function.comp_apply,
      ← horizontalBond_eq_translate]
  rw [← he]
  exact (ht (pt i 0)).measureReal_preimage (measurableSet_bondOpenEvent _).nullMeasurableSet

/-- Finite intersections of increasing bond events have probability at least the product
of their probabilities. -/
theorem bond_prod_measureReal_le_biInter (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {κ : Type*} (A : κ → Set (Sym2 (Site 2) → Bool)) (hA : ∀ i, IsUpperSet (A i))
    (hAm : ∀ i, MeasurableSet (A i)) (s : Finset κ) :
    ∏ i ∈ s, μ.real (A i) ≤ μ.real (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.set_biInter_insert]
    have hm : MeasurableSet (⋂ j ∈ s, A j) := Finset.measurableSet_biInter s fun j _ => hAm j
    have hu : IsUpperSet (⋂ j ∈ s, A j) := isUpperSet_iInter₂ fun j _ => hA j
    exact (mul_le_mul_of_nonneg_left ih measureReal_nonneg).trans
      (ha (A i) (⋂ j ∈ s, A j) (hA i) hu (hAm i) hm)

/-- If every bond of the bottom row is open, the rectangle is crossed horizontally. -/
theorem biInter_horizontalBond_subset_crossing (w h : ℕ) :
    (⋂ i ∈ Finset.range w, bondOpenEvent (horizontalBond i)) ⊆ bondCrossingEvent w h := by
  intro ω hω
  apply (mem_bondCrossingEvent_iff_lrCrossing w h ω).mpr
  apply mem_lrCrossing_of_bottomRowEdges_subset
  intro e he
  have he' : e ∈ bottomRowEdges w := he
  simp only [bottomRowEdges, Finset.mem_image, Finset.mem_range] at he'
  obtain ⟨i, hi, rfl⟩ := he'
  refine ⟨?_, ?_⟩
  · rw [lattice_eq_zdGraph]
    exact bottomRowEdges_subset_edgeSet w he
  · exact mem_iInter₂.mp hω i (Finset.mem_range.mpr hi)

/-- A horizontal rectangle crossing has probability at least the one-bond probability
raised to the number of bonds in its bottom row. -/
theorem horizontalBond_pow_le_crossing (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ) (w h : ℕ) :
    μ.real (bondOpenEvent (horizontalBond 0)) ^ w ≤ μ.real (bondCrossingEvent w h) := by
  let A : ℕ → Set (Sym2 (Site 2) → Bool) := fun i => bondOpenEvent (horizontalBond i)
  have hh := bond_prod_measureReal_le_biInter μ ha A
    (fun i => isUpperSet_bondOpenEvent _) (fun i => measurableSet_bondOpenEvent _)
    (Finset.range w)
  have hrow : μ.real (bondOpenEvent (horizontalBond 0)) ^ w ≤
      μ.real (⋂ i ∈ Finset.range w, A i) := by
    simp_rw [show ∀ i, μ.real (A i) = μ.real (bondOpenEvent (horizontalBond 0)) from
      fun i => measureReal_horizontalBond_eq μ ht i] at hh
    simpa only [Finset.prod_const, Finset.card_range] using hh
  exact hrow.trans (measureReal_mono (biInter_horizontalBond_subset_crossing w h)
    (measure_ne_top μ _))

/-- A bridge has probability at least the one-bond probability raised to `4m`. -/
theorem horizontalBond_pow_le_kstBridge (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ) (m : ℕ) :
    μ.real (bondOpenEvent (horizontalBond 0)) ^ (4 * m) ≤ μ.real (kstBridgeEvent m) :=
  (horizontalBond_pow_le_crossing μ ha ht (4 * m) (2 * m)).trans
    (measureReal_crossing_le_kstBridge μ ht m)

end Sandpile.External.RSW
