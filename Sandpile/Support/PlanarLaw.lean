/-
Symmetry, positive association and crossing probabilities for planar lattice fields.
-/
import Sandpile.Support.KernelSymmetry
import Sandpile.Support.RectangleTranspose
import LatticeProb.Prob.Harris

open MeasureTheory ProbabilityTheory Set
noncomputable section
namespace Sandpile

def planarFieldShift (v : Site 2) (F : Site 2 → ℝ) (z : Site 2) : ℝ := F (z + v)

def planarFieldTranspose (F : Site 2 → ℝ) (z : Site 2) : ℝ := F ![z 1, z 0]

def planarFieldReflect (F : Site 2 → ℝ) (z : Site 2) : ℝ := F ![-z 0, z 1]

def IsSymmetricPlanarLaw (μ : Measure (Site 2 → ℝ)) : Prop :=
  (∀ v : Site 2, MeasurePreserving (planarFieldShift v) μ μ) ∧
    MeasurePreserving planarFieldTranspose μ μ ∧ MeasurePreserving planarFieldReflect μ μ

def IsAssociatedPlanarLaw (μ : Measure (Site 2 → ℝ)) : Prop :=
  ∀ A B : Set (Site 2 → ℝ), IsUpperSet A → IsUpperSet B → MeasurableSet A → MeasurableSet B →
    μ.real A * μ.real B ≤ μ.real (A ∩ B)

def planarCrossingEvent (w h : ℕ) (level : ℝ) : Set (Site 2 → ℝ) :=
  {F | level ≤ crossingValue (planeRectangle w h) (fun z => F z)}

def probabilityInUnitInterval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) : Icc (0 : ℝ) 1 :=
  ⟨μ.real A, measureReal_nonneg, measureReal_le_one⟩

lemma isAssociatedPlanarLaw_map {Ω : Type*} [MeasurableSpace Ω] [Preorder Ω]
    (μ : Measure Ω) (H : Ω → (Site 2 → ℝ)) (hH : Measurable H) (hmono : Monotone H)
    (hbase : ∀ A B : Set Ω, IsUpperSet A → IsUpperSet B → MeasurableSet A → MeasurableSet B →
      μ.real A * μ.real B ≤ μ.real (A ∩ B)) : IsAssociatedPlanarLaw (μ.map H) := by
  intro A B hA hB hAm hBm
  have ha : IsUpperSet (H ⁻¹' A) := fun _ _ hxy hx => hA (hmono hxy) hx
  have hb : IsUpperSet (H ⁻¹' B) := fun _ _ hxy hx => hB (hmono hxy) hx
  have hh := hbase (H ⁻¹' A) (H ⁻¹' B) ha hb (hAm.preimage hH) (hBm.preimage hH)
  simpa only [Measure.real, Measure.map_apply hH hAm, Measure.map_apply hH hBm,
    Measure.map_apply hH (hAm.inter hBm), preimage_inter] using hh

lemma monotone_finiteKernelField {d : ℕ} {h : Site d → ℝ}
    (t : Finset (Site d)) (ht : ∀ u ∉ t, h u = 0) (hn : ∀ u, 0 ≤ h u) (z : Site d) :
    Monotone (fun ζ : Site d → ℝ => finiteKernelField h ζ z) := by
  intro ζ ξ hζ
  simp only [finiteKernelField_eq_sum t ht]
  exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hζ _) (hn u))

lemma isAssociatedPlanarLaw_finiteKernel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h : Site 4 → ℝ} (t : Finset (Site 4)) (ht : ∀ u ∉ t, h u = 0)
    (hn : ∀ u, 0 ≤ h u) (x : Site 4) :
    IsAssociatedPlanarLaw ((LatticeProb.iidLaw 4 μ).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 => finiteKernelField h ζ (planeTranslate x z))) := by
  apply isAssociatedPlanarLaw_map
  · exact measurable_pi_lambda _ (fun z => measurable_finiteKernelField t ht (planeTranslate x z))
  · intro ζ ξ hζ z
    exact monotone_finiteKernelField t ht hn (planeTranslate x z) hζ
  · intro A B hA hB hAm hBm
    exact LatticeProb.infinitePi_harris (fun _ : Site 4 => μ) hA hB hAm hBm

end Sandpile
