import Sandpile.Support.LinGaussBridge
import Sandpile.Support.LinGreenTail
import Sandpile.Support.LinStationary

/-! # Gaussian Threshold Shift

Translation invariance of the threshold events in the GAUSSIAN branch,
`sandpile.tex:5453-5454`:

  "In either case, the pair $(J,(u_m)_{m\geq0})$ has a translation-invariant
   law."

`Support/LinStationary.lean` proves this for the independent branch
`J = -G(0,0)ζ`, where the threshold field is a function of the scenery at the
single site and the shift of the field carries the event across.  In the
Gaussian branch `J = -V_∞` the field is the limit of the partial sums over the
boxes CENTRED AT THE ORIGIN, and shifting the scenery by `y` moves the origin's
box exhaustion to the exhaustion by the boxes centred at `y`.  The two limits
agree only almost surely, so the shift carries the threshold event across only
up to a null set, and the whole content of this file is that the null set is
measurable and null.

The route.  The partial sums are finite sums of coordinates, hence measurable,
so the set

  `greenShiftAgree d y = {ζ : the partial sums at y converge, and the difference
     of the partial sums at y and the shifted partial sums at the origin tends
     to zero}`

is measurable.  On it the two box limits are equal.  Under the standard Gaussian
product law it has full measure, because both sequences converge to the same
isonormal image (`ae_tendsto_greenPartialSum` along the boxes at the origin and
`ae_tendsto_greenPartialSum_shift` along the boxes at `y`).  Being measurable,
it transports along the two pushforwards that carry the standard Gaussian law to
the i.i.d. scenery and the i.i.d. scenery to the scenery of the centred mass
field.

Finally the shift itself is a measurable EQUIVALENCE of the field space, so its
measure preservation holds on every set, not only on the measurable ones: the
threshold event of the Gaussian branch is not known to be measurable, since the
field is only almost everywhere measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The centred mass law is invariant under the field shift, on every set. -/
theorem centeredMassLaw_preimage_shiftField_all (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (y : Site d) (S : Set (Site d → ℝ)) :
    (centeredMassLaw d ν) (shiftField y ⁻¹' S) = (centeredMassLaw d ν) S := by
  classical
  set μ : Measure ℝ := ν.map fun z => 1 + 2 * (d : ℝ) * z with hμ
  haveI : IsProbabilityMeasure μ := by
    rw [hμ]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hcm : centeredMassLaw d ν = massLaw d μ := by rw [centeredMassLaw, hμ]
  have hinv : ∀ σ : Site d → ℝ, shiftField (-y) (shiftField y σ) = σ := by
    intro σ
    funext z
    simp [shiftField]
  have hinv' : ∀ σ : Site d → ℝ, shiftField y (shiftField (-y) σ) = σ := by
    intro σ
    funext z
    simp [shiftField]
  let e : (Site d → ℝ) ≃ᵐ (Site d → ℝ) :=
    { toEquiv := ⟨shiftField y, shiftField (-y), hinv, hinv'⟩
      measurable_toFun := measurable_shiftField y
      measurable_invFun := measurable_shiftField (-y) }
  have he : ⇑e = shiftField (d := d) y := rfl
  rw [hcm]
  calc (massLaw d μ) (shiftField y ⁻¹' S)
      = (Measure.map (⇑e) (massLaw d μ)) S := by
        rw [MeasurableEquiv.map_apply e S, he]
    _ = (massLaw d μ) S := by rw [he, massLaw_map_shiftField]

/-- The partial sum of a shifted scaled scenery at the origin is the partial sum at `y`
along the boxes centred at `y`. -/
theorem infiniteGreenFieldPartial_shift_eq (n : ℕ) (c : ℝ) (omg : Site d → ℝ) (y : Site d) :
    infiniteGreenFieldPartial n (fun z => c * omg (z + y)) 0
      = c * ∑ w ∈ boxFinset y n, green d y w * omg w := by
  have hbox : boxFinset y n
      = (boxFinset (0 : Site d) n).map ⟨fun z => z + y, add_left_injective y⟩ := by
    ext w
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, mem_boxFinset_iff]
    constructor
    · intro hw
      refine ⟨w - y, ?_, by ring⟩
      rw [← boxDist_sub y w]
      exact hw
    · rintro ⟨z, hz, rfl⟩
      rw [boxDist_sub y (z + y)]
      simpa using hz
  have hgreen : ∀ z : Site d, green d 0 z = green d y (z + y) := by
    intro z
    rw [green_shift (0 : Site d) z, green_shift y (z + y)]
    congr 1
    abel
  rw [infiniteGreenFieldPartial,
    Finset.sum_set_coe (f := fun z : Site d => green d 0 z * (c * omg (z + y)))
      (greenFieldBox d n),
    greenFieldBox_toFinset, hbox, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [hgreen z]
  ring

/-- The set of sceneries along which the two box exhaustions of the Green field agree
is measurable. -/
theorem measurableSet_greenShiftAgree (y : Site d) :
    MeasurableSet {zeta : Site d → ℝ |
      (∃ L : ℝ, Tendsto (fun n => infiniteGreenFieldPartial n zeta y) atTop (𝓝 L)) ∧
      Tendsto (fun n => infiniteGreenFieldPartial n zeta y
        - infiniteGreenFieldPartial n (fun z => zeta (z + y)) 0) atTop (𝓝 0)} := by
  have hm1 : ∀ n : ℕ, Measurable (fun zeta : Site d → ℝ => infiniteGreenFieldPartial n zeta y) :=
    fun n => measurable_infiniteGreenFieldPartial n y
  have hm2 : ∀ n : ℕ, Measurable (fun zeta : Site d → ℝ =>
      infiniteGreenFieldPartial n (fun z => zeta (z + y)) 0) := by
    intro n
    unfold infiniteGreenFieldPartial
    exact Finset.measurable_sum _ fun z _ => (measurable_pi_apply ((z : Site d) + y)).const_mul _
  exact (measurableSet_exists_tendsto hm1).inter
    (measurableSet_tendsto (𝓝 (0:ℝ)) fun n => (hm1 n).sub (hm2 n))

/-- On the agreement set the two box exhaustions define the same Green field value. -/
theorem infiniteGreenField_shift_of_mem (y : Site d) (zeta : Site d → ℝ)
    (h1 : ∃ L : ℝ, Tendsto (fun n => infiniteGreenFieldPartial n zeta y) atTop (𝓝 L))
    (h2 : Tendsto (fun n => infiniteGreenFieldPartial n zeta y
        - infiniteGreenFieldPartial n (fun z => zeta (z + y)) 0) atTop (𝓝 0)) :
    infiniteGreenField (fun z => zeta (z + y)) 0 = infiniteGreenField zeta y := by
  obtain ⟨L, hL⟩ := h1
  have hB : Tendsto (fun n => infiniteGreenFieldPartial n (fun z => zeta (z + y)) 0) atTop
      (𝓝 L) := by
    have hsub := hL.sub h2
    simpa [sub_sub_cancel] using hsub
  have hexA : ∃ M : ℝ, Tendsto (fun n => infiniteGreenFieldPartial n zeta y) atTop (𝓝 M) := ⟨L, hL⟩
  have hexB : ∃ M : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n (fun z => zeta (z + y)) 0) atTop (𝓝 M) :=
    ⟨L, hB⟩
  have hA : infiniteGreenField zeta y = L := by
    rw [infiniteGreenField, dif_pos hexA]
    exact tendsto_nhds_unique (Classical.choose_spec hexA) hL
  have hBv : infiniteGreenField (fun z => zeta (z + y)) 0 = L := by
    rw [infiniteGreenField, dif_pos hexB]
    exact tendsto_nhds_unique (Classical.choose_spec hexB) hB
  rw [hA, hBv]

/-- Almost every scaled standard Gaussian scenery lies in the agreement set of the two
box exhaustions. -/
theorem ae_mem_greenShiftAgree_gauss (hd : 5 ≤ d) (c : ℝ) (y : Site d)
    (hpart : ∀ (n : ℕ) (omg : Site d → ℝ),
      infiniteGreenFieldPartial n (fun z => c * omg (z + y)) 0
        = c * ∑ w ∈ boxFinset y n, green d y w * omg w) :
    ∀ᵐ omg ∂(LatticeProb.gaussLaw (Site d)),
      (∃ L : ℝ,
          Tendsto (fun n => infiniteGreenFieldPartial n (fun z => c * omg z) y) atTop (𝓝 L)) ∧
        Tendsto (fun n => infiniteGreenFieldPartial n (fun z => c * omg z) y
          - infiniteGreenFieldPartial n (fun z => c * omg (z + y)) 0) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_greenPartialSum hd y, ae_tendsto_greenPartialSum_shift hd y y]
    with omg h0 hy
  have hA : Tendsto (fun n => infiniteGreenFieldPartial n (fun z => c * omg z) y) atTop
      (𝓝 (c * ⇑(LatticeProb.gaussIso (greenLp d hd y)) omg)) := by
    simp only [infiniteGreenFieldPartial_smul]
    exact h0.const_mul c
  have hB : Tendsto (fun n => infiniteGreenFieldPartial n (fun z => c * omg (z + y)) 0) atTop
      (𝓝 (c * ⇑(LatticeProb.gaussIso (greenLp d hd y)) omg)) := by
    simp only [hpart]
    exact hy.const_mul c
  refine ⟨⟨c * ⇑(LatticeProb.gaussIso (greenLp d hd y)) omg, hA⟩, ?_⟩
  have hsub := hA.sub hB
  simpa using hsub

/-- A measurable almost-sure property of the scaled standard Gaussian field is an
almost-sure property of the i.i.d. Gaussian scenery. -/
theorem ae_of_ae_gauss (v : ℝ≥0) (P : (Site d → ℝ) → Prop)
    (hms : MeasurableSet {zeta : Site d → ℝ | P zeta})
    (hgauss : ∀ᵐ omg ∂(LatticeProb.gaussLaw (Site d)), P (fun z => Real.sqrt (v : ℝ) * omg z)) :
    ∀ᵐ zeta ∂(LatticeProb.iidLaw d (gaussianReal 0 v)), P zeta := by
  rw [iidLaw_gaussianReal_eq_map d v]
  have hS : Measurable fun (omg : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * omg z := by
    fun_prop
  rw [ae_map_iff hS.aemeasurable hms]
  exact hgauss

/-- A measurable almost-sure property of the i.i.d. scenery is an almost-sure property of
the scenery read off the centred mass field. -/
theorem ae_scenery_of_ae_iid (d : ℕ) (hd1 : 1 ≤ d) (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (P : (Site d → ℝ) → Prop) (hms : MeasurableSet {zeta : Site d → ℝ | P zeta})
    (hiid : ∀ᵐ zeta ∂(LatticeProb.iidLaw d nu), P zeta) :
    ∀ᵐ sigma ∂(centeredMassLaw d nu), P (scenery d sigma) := by
  have hmap := map_scenery_centeredMassLaw d nu hd1
  rw [← hmap] at hiid
  exact (ae_map_iff (measurable_scenery d).aemeasurable hms).mp hiid

/-- Two events with almost surely equal second components have almost surely equal
symmetric differences with a fixed first component. -/
theorem symmDiff_ae_congr_right {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha)
    (A C B : Set alpha) (h : C =ᵐ[mu] B) :
    (symmDiff A C : Set alpha) =ᵐ[mu] (symmDiff A B : Set alpha) := by
  rw [Filter.eventuallyEq_set] at h ⊢
  filter_upwards [h] with x hx
  simp only [Set.mem_symmDiff, hx]

/-- The measure of a symmetric difference does not see an almost sure change of the second
component. -/
theorem measure_symmDiff_congr_right {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha)
    (A C B : Set alpha) (h : C =ᵐ[mu] B) : mu (symmDiff A C) = mu (symmDiff A B) :=
  measure_congr (symmDiff_ae_congr_right mu A C B h)

/-- **The two box exhaustions agree almost surely, in the mass normalization.**  Shifting
the mass field by `y` moves the Gaussian Green field at the origin to the field at `y`. -/
theorem ae_infiniteGreenField_scenery_shift (hd : 5 ≤ d) (v : ℝ≥0) (y : Site d) :
    ∀ᵐ σ ∂(centeredMassLaw d (gaussianReal 0 v)),
      infiniteGreenField (scenery d (shiftField y σ)) 0
        = infiniteGreenField (scenery d σ) y := by
  have hms := measurableSet_greenShiftAgree (d := d) y
  have hg := ae_mem_greenShiftAgree_gauss hd (Real.sqrt (v : ℝ)) y
    (fun n omg => infiniteGreenFieldPartial_shift_eq n (Real.sqrt (v : ℝ)) omg y)
  have hiid := ae_of_ae_gauss v _ hms hg
  have hmass := ae_scenery_of_ae_iid d (by omega) (gaussianReal 0 v) _ hms hiid
  filter_upwards [hmass] with σ hσ
  exact infiniteGreenField_shift_of_mem y (scenery d σ) hσ.1 hσ.2

/-- **The threshold events translate, in the Gaussian branch.**  With
`J(x) = -V_∞(x)`, the symmetric difference of the contact event and the threshold
event at a site has the same probability as at the origin.  This is the Gaussian half of
`sandpile.tex:5448-5449`, the half that `Support/LinStationary.lean` left open. -/
theorem measure_threshold_symmDiff_shift_gauss (hd : 5 ≤ d) (v : ℝ≥0)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x)
    (m : ℕ) (b : ℝ) (y : Site d) :
    (centeredMassLaw d (gaussianReal 0 v))
        (symmDiff {σ : Site d → ℝ | odometer σ m y = 0} {σ : Site d → ℝ | b < J σ y})
      = (centeredMassLaw d (gaussianReal 0 v))
        (symmDiff {σ : Site d → ℝ | odometer σ m 0 = 0} {σ : Site d → ℝ | b < J σ 0}) := by
  classical
  have hae := ae_infiniteGreenField_scenery_shift hd v y
  have hodo : shiftField y ⁻¹' {σ : Site d → ℝ | odometer σ m 0 = 0}
      = {σ : Site d → ℝ | odometer σ m y = 0} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, odometer_shiftField σ y m 0, zero_add]
  have hpre : shiftField y ⁻¹'
      (symmDiff {σ : Site d → ℝ | odometer σ m 0 = 0} {σ : Site d → ℝ | b < J σ 0})
      = symmDiff {σ : Site d → ℝ | odometer σ m y = 0}
          (shiftField y ⁻¹' {σ : Site d → ℝ | b < J σ 0}) := by
    rw [Set.preimage_symmDiff, hodo]
  have hCB : (shiftField y ⁻¹' {σ : Site d → ℝ | b < J σ 0})
      =ᵐ[centeredMassLaw d (gaussianReal 0 v)] {σ : Site d → ℝ | b < J σ y} := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hae] with σ hσ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hJ, hσ]
  calc (centeredMassLaw d (gaussianReal 0 v))
        (symmDiff {σ : Site d → ℝ | odometer σ m y = 0} {σ : Site d → ℝ | b < J σ y})
      = (centeredMassLaw d (gaussianReal 0 v))
          (symmDiff {σ : Site d → ℝ | odometer σ m y = 0}
            (shiftField y ⁻¹' {σ : Site d → ℝ | b < J σ 0})) :=
        (measure_symmDiff_congr_right (centeredMassLaw d (gaussianReal 0 v))
          {σ : Site d → ℝ | odometer σ m y = 0}
          (shiftField y ⁻¹' {σ : Site d → ℝ | b < J σ 0})
          {σ : Site d → ℝ | b < J σ y} hCB).symm
    _ = (centeredMassLaw d (gaussianReal 0 v)) (shiftField y ⁻¹'
          (symmDiff {σ : Site d → ℝ | odometer σ m 0 = 0} {σ : Site d → ℝ | b < J σ 0})) := by
        rw [hpre]
    _ = (centeredMassLaw d (gaussianReal 0 v))
          (symmDiff {σ : Site d → ℝ | odometer σ m 0 = 0} {σ : Site d → ℝ | b < J σ 0}) :=
        centeredMassLaw_preimage_shiftField_all (gaussianReal 0 v) y _


end Sandpile
