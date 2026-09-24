/-
The law of the Gaussian Green field under the i.i.d. scenery.

`Support/LinGaussField.lean` identifies the finite-dimensional laws of
`eq:dgt4-infinite-green-field` under the standard Gaussian product law pushed
forward by the scaling `ω ↦ √v ω`.  The estimates of `ssec:expl-d5` are carried
out under `LatticeProb.iidLaw d (gaussianReal 0 v)`, and the main theorems under
`centeredMassLaw d ν`, so the law has to be transported along those two
identifications.  Pushing a measure forward twice needs the field to be almost
everywhere measurable, and the field is defined by a case split on the existence
of the box limit, so the transport goes through the convergence set: the partial
sums are finite sums of coordinates, hence measurable; the set where they
converge is therefore measurable; that set has full measure under the i.i.d.
Gaussian law; and on it the field is the limit of the partial sums, so it is an
almost everywhere limit of measurable functions.
-/
import Sandpile.Support.LinGaussField
import Sandpile.Support.SceneryBridge

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The finite-box partial sum of `eq:dgt4-infinite-green-field` is a measurable
function of the scenery: it is a finite sum of coordinates. -/
theorem measurable_infiniteGreenFieldPartial (n : ℕ) (x : Site d) :
    Measurable (fun ζ : Site d → ℝ => infiniteGreenFieldPartial n ζ x) := by
  unfold infiniteGreenFieldPartial
  exact Finset.measurable_sum _ fun z _ => (measurable_pi_apply (z : Site d)).const_mul _

/-- The partial sum of a scaled scenery. -/
theorem infiniteGreenFieldPartial_smul (n : ℕ) (c : ℝ) (ω : Site d → ℝ) (x : Site d) :
    infiniteGreenFieldPartial n (fun z => c * ω z) x
      = c * ∑ z ∈ boxFinset (0 : Site d) n, green d x z * ω z := by
  rw [infiniteGreenFieldPartial,
    Finset.sum_set_coe (f := fun z : Site d => green d x z * (c * ω z)) (greenFieldBox d n),
    greenFieldBox_toFinset, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- The set of sceneries along which the box limit of
`eq:dgt4-infinite-green-field` exists is measurable: convergence of a sequence of
measurable functions is a measurable condition. -/
theorem measurableSet_greenFieldConv (x : Site d) :
    MeasurableSet {ζ : Site d → ℝ |
      ∃ L : ℝ, Tendsto (fun n => infiniteGreenFieldPartial n ζ x) atTop (𝓝 L)} :=
  measurableSet_exists_tendsto fun n => measurable_infiniteGreenFieldPartial n x

/-- Under the i.i.d. centred Gaussian scenery the box limit exists almost surely. -/
theorem ae_mem_greenFieldConv_iid (hd : 5 ≤ d) (v : ℝ≥0) (x : Site d) :
    ∀ᵐ ζ ∂(LatticeProb.iidLaw d (gaussianReal 0 v)),
      ∃ L : ℝ, Tendsto (fun n => infiniteGreenFieldPartial n ζ x) atTop (𝓝 L) := by
  rw [iidLaw_gaussianReal_eq_map d v]
  have hS : Measurable fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z := by
    fun_prop
  rw [ae_map_iff hS.aemeasurable (measurableSet_greenFieldConv x)]
  filter_upwards [ae_tendsto_greenPartialSum hd x] with ω hω
  refine ⟨Real.sqrt (v : ℝ) * ⇑(LatticeProb.gaussIso (greenLp d hd x)) ω, ?_⟩
  simp only [infiniteGreenFieldPartial_smul]
  exact hω.const_mul _

/-- The Gaussian Green field is almost everywhere measurable under the i.i.d.
Gaussian scenery: on the full-measure set where the box limit exists it is the
limit of the measurable partial sums. -/
theorem aemeasurable_infiniteGreenField_iid (hd : 5 ≤ d) (v : ℝ≥0) (x : Site d) :
    AEMeasurable (fun ζ : Site d → ℝ => infiniteGreenField ζ x)
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  refine aemeasurable_of_tendsto_metrizable_ae'
    (fun n => (measurable_infiniteGreenFieldPartial n x).aemeasurable) ?_
  filter_upwards [ae_mem_greenFieldConv_iid hd v x] with ζ hζ
  rw [infiniteGreenField, dif_pos hζ]
  exact Classical.choose_spec hζ

/-- **The finite-dimensional laws of the Gaussian Green field under the i.i.d.
scenery.**  The vector `(V_∞(x))_{x∈Λ}` of `eq:dgt4-infinite-green-field` is a
centred Gaussian vector with covariance `Var(ζ(0)) ∑_z G(x,z)G(y,z)`. -/
theorem map_infiniteGreenField_vector_iid (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d) :
    (LatticeProb.iidLaw d (gaussianReal 0 v)).map
        (fun ζ => (WithLp.toLp 2 (fun i => infiniteGreenField ζ (xs i)) :
          EuclideanSpace ℝ (Fin m)))
      = multivariateGaussian 0
          (Matrix.of fun i j =>
            (v : ℝ) * ∑' z : Site d, green d (xs i) z * green d (xs j) z) := by
  classical
  have hA : ∀ i : Fin m, AEMeasurable (fun ζ : Site d → ℝ => infiniteGreenField ζ (xs i))
      (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
    fun i => aemeasurable_infiniteGreenField_iid hd v (xs i)
  choose g hgm hg using hA
  have hSm : Measurable (fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z) := by
    fun_prop
  have hG : Measurable (fun ζ : Site d → ℝ =>
      (WithLp.toLp 2 (fun i => g i ζ) : EuclideanSpace ℝ (Fin m))) := by
    fun_prop
  have hae1 : (fun ζ : Site d → ℝ =>
        (WithLp.toLp 2 (fun i => infiniteGreenField ζ (xs i)) : EuclideanSpace ℝ (Fin m)))
      =ᵐ[LatticeProb.iidLaw d (gaussianReal 0 v)]
      (fun ζ : Site d → ℝ =>
        (WithLp.toLp 2 (fun i => g i ζ) : EuclideanSpace ℝ (Fin m))) := by
    filter_upwards [ae_all_iff.2 hg] with ζ hζ
    congr 1
    funext i
    exact hζ i
  rw [Measure.map_congr hae1, iidLaw_gaussianReal_eq_map d v, Measure.map_map hG hSm]
  have h2 : ∀ i : Fin m, ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      infiniteGreenField (fun z => Real.sqrt (v : ℝ) * ω z) (xs i)
        = g i (fun z => Real.sqrt (v : ℝ) * ω z) := by
    intro i
    have hi := hg i
    rw [iidLaw_gaussianReal_eq_map d v] at hi
    exact ae_of_ae_map hSm.aemeasurable hi
  have hae2 : ((fun ζ : Site d → ℝ =>
        (WithLp.toLp 2 (fun i => g i ζ) : EuclideanSpace ℝ (Fin m)))
        ∘ (fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z))
      =ᵐ[LatticeProb.gaussLaw (Site d)]
      (fun ω : Site d → ℝ => (WithLp.toLp 2
        (fun i => infiniteGreenField (fun z => Real.sqrt (v : ℝ) * ω z) (xs i)) :
        EuclideanSpace ℝ (Fin m))) := by
    filter_upwards [ae_all_iff.2 h2] with ω hω
    simp only [Function.comp_apply]
    congr 1
    funext i
    exact (hω i).symm
  rw [Measure.map_congr hae2]
  exact map_infiniteGreenField_vector hd v xs

/-- The vector of Gaussian Green fields at finitely many sites is almost
everywhere measurable under the i.i.d. Gaussian scenery. -/
theorem aemeasurable_greenFieldVector_iid (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d) :
    AEMeasurable (fun ζ : Site d → ℝ =>
        (WithLp.toLp 2 (fun i => infiniteGreenField ζ (xs i)) : EuclideanSpace ℝ (Fin m)))
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  classical
  choose g hgm hg using fun i : Fin m => aemeasurable_infiniteGreenField_iid hd v (xs i)
  refine ⟨fun ζ => (WithLp.toLp 2 (fun i => g i ζ) : EuclideanSpace ℝ (Fin m)), by fun_prop, ?_⟩
  filter_upwards [ae_all_iff.2 hg] with ζ hζ
  congr 1
  funext i
  exact hζ i

/-- **The finite-dimensional laws of the Gaussian Green field in the mass
normalization.**  This is the form the proof of `lem:dgt4-path-survival` uses:
the scenery of `sandpile.tex:5449-5450` is `ζ = (σ-1)/(2d)` with `σ` distributed
according to `centeredMassLaw d ν`, and for a centred Gaussian one-site law the
vector `(V_∞(x))_{x∈Λ}` is the centred Gaussian vector whose covariance is the
Green Gram matrix. -/
theorem map_infiniteGreenField_vector_mass (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ}
    (xs : Fin m → Site d) :
    (centeredMassLaw d (gaussianReal 0 v)).map
        (fun σ => (WithLp.toLp 2 (fun i => infiniteGreenField (scenery d σ) (xs i)) :
          EuclideanSpace ℝ (Fin m)))
      = multivariateGaussian 0
          (Matrix.of fun i j =>
            (v : ℝ) * ∑' z : Site d, green d (xs i) z * green d (xs j) z) := by
  have hd1 : 1 ≤ d := by omega
  have hmap : (centeredMassLaw d (gaussianReal 0 v)).map (scenery d)
      = LatticeProb.iidLaw d (gaussianReal 0 v) :=
    map_scenery_centeredMassLaw d (gaussianReal 0 v) hd1
  have hGa : AEMeasurable (fun ζ : Site d → ℝ =>
      (WithLp.toLp 2 (fun i => infiniteGreenField ζ (xs i)) : EuclideanSpace ℝ (Fin m)))
      ((centeredMassLaw d (gaussianReal 0 v)).map (scenery d)) := by
    rw [hmap]
    exact aemeasurable_greenFieldVector_iid hd v xs
  have hsc : AEMeasurable (scenery (d := d)) (centeredMassLaw d (gaussianReal 0 v)) :=
    (measurable_scenery d).aemeasurable
  have hcomp := AEMeasurable.map_map_of_aemeasurable hGa hsc
  rw [hmap] at hcomp
  rw [show (fun σ : Site d → ℝ => (WithLp.toLp 2
      (fun i => infiniteGreenField (scenery d σ) (xs i)) : EuclideanSpace ℝ (Fin m)))
      = ((fun ζ : Site d → ℝ => (WithLp.toLp 2
        (fun i => infiniteGreenField ζ (xs i)) : EuclideanSpace ℝ (Fin m))) ∘ scenery d) from rfl,
    ← hcomp]
  exact map_infiniteGreenField_vector_iid hd v xs

end Sandpile
