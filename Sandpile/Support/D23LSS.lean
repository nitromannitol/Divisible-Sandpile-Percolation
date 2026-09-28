import Sandpile.Support.D23Field
import Sandpile.Support.D4CritLSS

/-!
# Measurability and stationarity of the dimension two/three good-block process

Two of the three hypotheses of \citet[Corollary~1.4]{LSS} for the good-block
process of the dimension-two and dimension-three percolation argument
(`sandpile.tex:2585-2590`): measurability and stationarity.  Stationarity is the
translation covariance of the localized odometer field together with the shift
invariance of the i.i.d. scenery law. The measurability half is proved by
`measurableSet_blockGood_d23Field` and `measurable_decide_blockGood_d23Field`, writing
`BlockGood` as a finite intersection of level-set-crossing conditions on `crossingValue`;
stationarity combines the shift covariance `blockGood_d23Field_shift` of the localized field
`d23Field` with the shift-invariance `massLaw_map_shiftField` of the i.i.d. scenery law to give
`blockGood_d23Field_law_stationary`.
-/

open MeasureTheory

noncomputable section
namespace Sandpile

open scoped Classical

variable {d : ℕ}

/-- Stationarity: the good block at `z + w` for the scenery is the good block at
`z` for the translated scenery. -/
theorem blockGood_d23Field_shift (hd : 1 ≤ d) (R t : ℕ) (ℓ : ℝ) (ζ : Site d → ℝ)
    (z w : Site 2) :
    BlockGood R (d23Field d R t ζ) ℓ (z + w)
      ↔ BlockGood R
          (d23Field d R t (shiftField (planeSite ![2 * (R : ℤ) * w 0, 2 * (R : ℤ) * w 1]) ζ))
          ℓ z := by
  refine blockGood_congr R _ _ ℓ (z + w) z fun v => ?_
  rw [d23Field_shift hd, blockShift_add]

/-- The good-block event `{ζ | BlockGood R (d23Field d R t ζ) ℓ z}` is measurable in the
scenery `ζ`, since `BlockGood` unfolds to a finite intersection of four crossing-threshold
conditions `ℓ ≤ crossingValue Q (...)` on the localized field `d23Field`, each measurable
because `crossingValue` is measurable in the field and `d23Field` is measurable in `ζ`. -/
theorem measurableSet_blockGood_d23Field (hd : 1 ≤ d) (R t : ℕ) (ℓ : ℝ) (z : Site 2) :
    MeasurableSet {ζ : Site d → ℝ | BlockGood R (d23Field d R t ζ) ℓ z} := by
  have hm : ∀ (Q : Finset (Site 2)), IsLatticeRectangle Q → Q.Nonempty →
      Measurable (fun ζ : Site d → ℝ =>
        crossingValue Q (fun v : Q => d23Field d R t ζ (blockShift R z (v : Site 2)))) :=
    fun Q hQ hN => (measurable_crossingValue hQ hN).comp
      (measurable_pi_lambda _ fun v => measurable_d23Field hd R t _)
  have h1 : MeasurableSet {ζ : Site d → ℝ | ℓ ≤ crossingValue (planeRectangle (2 * R) (2 * R))
      (fun v => d23Field d R t ζ (blockShift R z (v : Site 2)))} :=
    measurableSet_le measurable_const
      (hm _ (isLatticeRectangle_planeRectangle (2 * R) (2 * R))
        (planeRectangle_nonempty (2 * R) (2 * R)))
  have h2 : MeasurableSet {ζ : Site d → ℝ | ℓ ≤ crossingValue (planeRectangle (2 * R) (2 * R))
      (fun v => d23Field d R t ζ
        (blockShift R z ((transposeRectangle (2 * R) (2 * R) v : planeRectangle (2 * R) (2 * R)) :
          Site 2)))} :=
    measurableSet_le measurable_const
      ((measurable_crossingValue (isLatticeRectangle_planeRectangle (2 * R) (2 * R))
        (planeRectangle_nonempty (2 * R) (2 * R))).comp
        (measurable_pi_lambda _ fun v => measurable_d23Field hd R t _))
  have h3 : MeasurableSet {ζ : Site d → ℝ | ℓ ≤ crossingValue (planeRectangle (4 * R) (2 * R))
      (fun v => d23Field d R t ζ (blockShift R z (v : Site 2)))} :=
    measurableSet_le measurable_const
      (hm _ (isLatticeRectangle_planeRectangle (4 * R) (2 * R))
        (planeRectangle_nonempty (4 * R) (2 * R)))
  have h4 : MeasurableSet {ζ : Site d → ℝ | ℓ ≤ crossingValue (planeRectangle (4 * R) (2 * R))
      (fun v => d23Field d R t ζ
        (blockShift R z ((transposeRectangle (4 * R) (2 * R) v : planeRectangle (2 * R) (4 * R)) :
          Site 2)))} :=
    measurableSet_le measurable_const
      ((measurable_crossingValue (isLatticeRectangle_planeRectangle (4 * R) (2 * R))
        (planeRectangle_nonempty (4 * R) (2 * R))).comp
        (measurable_pi_lambda _ fun v => measurable_d23Field hd R t _))
  exact h1.inter (h2.inter (h3.inter h4))

/-- The Boolean indicator `ζ ↦ decide (BlockGood R (d23Field d R t ζ) ℓ z)` is measurable,
since its preimage of `{true}` is exactly the measurable set of
`measurableSet_blockGood_d23Field`. -/
theorem measurable_decide_blockGood_d23Field (hd : 1 ≤ d) (R t : ℕ) (ℓ : ℝ) (z : Site 2) :
    Measurable (fun ζ : Site d → ℝ => decide (BlockGood R (d23Field d R t ζ) ℓ z)) := by
  refine measurable_to_bool ?_
  have hpre : (fun ζ : Site d → ℝ => decide (BlockGood R (d23Field d R t ζ) ℓ z))
      ⁻¹' {true} = {ζ : Site d → ℝ | BlockGood R (d23Field d R t ζ) ℓ z} := by
    ext ζ
    simp
  rw [hpre]
  exact measurableSet_blockGood_d23Field hd R t ℓ z

/-- Stationarity of the good-block process under the i.i.d. scenery law. -/
theorem blockGood_d23Field_law_stationary (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (R t : ℕ) (ℓ : ℝ) (w : Site 2) :
    Measure.map
        (fun (ζ : Site d → ℝ) (z : Site 2) =>
          decide (BlockGood R (d23Field d R t ζ) ℓ (z + w))) (LatticeProb.iidLaw d ν)
      = Measure.map
        (fun (ζ : Site d → ℝ) (z : Site 2) =>
          decide (BlockGood R (d23Field d R t ζ) ℓ z)) (LatticeProb.iidLaw d ν) := by
  set y : Site d := planeSite ![2 * (R : ℤ) * w 0, 2 * (R : ℤ) * w 1] with hy
  have hmeasG : Measurable (fun (ζ : Site d → ℝ) (z : Site 2) =>
      decide (BlockGood R (d23Field d R t ζ) ℓ z)) :=
    measurable_pi_lambda _ fun z => measurable_decide_blockGood_d23Field hd R t ℓ z
  have hfun : (fun (ζ : Site d → ℝ) (z : Site 2) =>
        decide (BlockGood R (d23Field d R t ζ) ℓ (z + w)))
      = (fun (ζ : Site d → ℝ) (z : Site 2) =>
          decide (BlockGood R (d23Field d R t ζ) ℓ z)) ∘ shiftField y := by
    funext ζ z
    simp only [Function.comp_apply]
    exact decide_eq_decide.mpr (blockGood_d23Field_shift hd R t ℓ ζ z w)
  rw [hfun, ← Measure.map_map hmeasG (measurable_shiftField y)]
  congr 1
  exact massLaw_map_shiftField d ν y

end Sandpile
