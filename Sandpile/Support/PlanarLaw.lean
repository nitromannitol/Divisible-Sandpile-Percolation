import Sandpile.Support.KernelSymmetry
import Sandpile.Support.RectangleTranspose
import LatticeProb.Prob.Harris

/-!
# Symmetry and association for planar lattice fields

Basic geometric symmetries (translation, coordinate transpose, reflection) of a field on
`Site 2`, and the two structural predicates on a law on `Site 2 → ℝ` used throughout the
percolation argument: `IsSymmetricPlanarLaw`, invariance under those symmetries, and
`IsAssociatedPlanarLaw`, the FKG/Harris positive-association inequality on upper sets.
Association is shown to pass to a monotone pushforward, and the i.i.d. law pushed forward
through a finite, nonnegative kernel field satisfies it by the Harris inequality for infinite
products.
-/

open MeasureTheory ProbabilityTheory Set
noncomputable section
namespace Sandpile

/-- The field `F` translated by the vector `v`: `planarFieldShift v F z = F (z + v)`. -/
def planarFieldShift (v : Site 2) (F : Site 2 → ℝ) (z : Site 2) : ℝ := F (z + v)

/-- The field `F` composed with the coordinate swap: `planarFieldTranspose F z = F ![z 1, z 0]`. -/
def planarFieldTranspose (F : Site 2 → ℝ) (z : Site 2) : ℝ := F ![z 1, z 0]

/-- The field `F` reflected across the second coordinate axis:
`planarFieldReflect F z = F ![-z 0, z 1]`. -/
def planarFieldReflect (F : Site 2 → ℝ) (z : Site 2) : ℝ := F ![-z 0, z 1]

/-- A law on planar fields is symmetric when it is invariant under every translation
`planarFieldShift v`, under the coordinate transpose `planarFieldTranspose`, and under the
reflection `planarFieldReflect`. -/
def IsSymmetricPlanarLaw (μ : Measure (Site 2 → ℝ)) : Prop :=
  (∀ v : Site 2, MeasurePreserving (planarFieldShift v) μ μ) ∧
    MeasurePreserving planarFieldTranspose μ μ ∧ MeasurePreserving planarFieldReflect μ μ

/-- A law on planar fields is (positively) associated when
`μ.real A * μ.real B ≤ μ.real (A ∩ B)` for all measurable upper sets `A` and `B`. -/
def IsAssociatedPlanarLaw (μ : Measure (Site 2 → ℝ)) : Prop :=
  ∀ A B : Set (Site 2 → ℝ), IsUpperSet A → IsUpperSet B → MeasurableSet A → MeasurableSet B →
    μ.real A * μ.real B ≤ μ.real (A ∩ B)

/-- The event that the field `F` crosses the `w × h` rectangle `planeRectangle w h` at level
`level`, i.e. `level ≤ crossingValue (planeRectangle w h) F`. -/
def planarCrossingEvent (w h : ℕ) (level : ℝ) : Set (Site 2 → ℝ) :=
  {F | level ≤ crossingValue (planeRectangle w h) (fun z => F z)}

/-- The probability `μ.real A` of a measurable set `A`, packaged as an element of the interval
`Icc (0:ℝ) 1` via `measureReal_nonneg` and `measureReal_le_one`. -/
def probabilityInUnitInterval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) : Icc (0 : ℝ) 1 :=
  ⟨μ.real A, measureReal_nonneg, measureReal_le_one⟩

/-- The pushforward of an associated law under a measurable, monotone map is again associated:
pulling back an upper set along a monotone map gives an upper set, so the association inequality
for `μ` transfers to `μ.map H`. -/
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

/-- For `h` supported on the finite set `t` and nonnegative, the finite kernel field
`ζ ↦ finiteKernelField h ζ z` is monotone in `ζ`: by `finiteKernelField_eq_sum` it agrees with a
finite sum over `t` whose summands are each monotone in `ζ`, since `h ≥ 0`. -/
lemma monotone_finiteKernelField {d : ℕ} {h : Site d → ℝ}
    (t : Finset (Site d)) (ht : ∀ u ∉ t, h u = 0) (hn : ∀ u, 0 ≤ h u) (z : Site d) :
    Monotone (fun ζ : Site d → ℝ => finiteKernelField h ζ z) := by
  intro ζ ξ hζ
  simp only [finiteKernelField_eq_sum t ht]
  exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hζ _) (hn u))

/-- The pushforward of the i.i.d. law `LatticeProb.iidLaw 4 μ` under the finite, nonnegative
kernel field `ζ ↦ finiteKernelField h ζ`, evaluated at `planeTranslate x z`, is an associated
law, by the Harris inequality for infinite products (`LatticeProb.infinitePi_harris`) together
with the monotonicity of `monotone_finiteKernelField`. -/
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
