import Sandpile.Support.D4CritStationary
import Sandpile.Support.D4CritBlock
import Sandpile.Support.D4PlaneEmbed
import Sandpile.Support.CrossingContinuity
import Sandpile.Support.ExitAverage
import Sandpile.Support.Killed

/-!
# Measurability and stationarity of the dimension-four good-block process

The three hypotheses of \citet[Corollary~1.4]{LSS} for the good-block process of
the dimension-four percolation argument (`sandpile.tex:3991-3995`):
measurability, stationarity and finite-range dependence.  Stationarity is the
translation covariance of the finite-range field of
`lem:d4-finite-range-lower-bound` together with the shift invariance of the
i.i.d. scenery law. The field `frBlockField` combines the finite-time killed Green field with the
localized exit term, and is shown shift-covariant by `frBlockField_shift`, which upgrades to
the good-block covariance `blockGood_frBlockField_shift` via the coordinate-plane translation
identities `planeEmbed_add`/`blockShift_add`/`blockGood_congr`. Measurability of the good-block
event is built up through `measurable_frGreenFieldTime`, `measurable_frExitValue`,
`measurable_frBlockField`, `measurableSet_blockGood_frBlockField` and
`measurable_decide_blockGood`, and combined with the shift invariance of the i.i.d. scenery law
(`massLaw_map_shiftField`) to give the stationarity of the good-block process under that law,
`blockGood_law_stationary`.
-/

open MeasureTheory

noncomputable section
namespace Sandpile

open scoped Classical

/-- The plane embedding is additive. -/
theorem planeEmbed_add (a b : Site 2) :
    planeEmbed (a + b) = planeEmbed a + planeEmbed b := by
  funext i
  by_cases hi : (i : ℕ) < 2
  · rw [planeEmbed_apply_lt _ _ hi]
    simp only [Pi.add_apply, planeEmbed_apply_lt _ _ hi]
  · rw [planeEmbed_apply_ge _ _ hi]
    simp only [Pi.add_apply, planeEmbed_apply_ge _ _ hi]
    ring

/-- The block anchored at `z + w` is the block anchored at `z` translated. -/
theorem blockShift_add (r : ℕ) (z w v : Site 2) :
    blockShift r (z + w) v
      = blockShift r z v + ![2 * (r : ℤ) * w 0, 2 * (r : ℤ) * w 1] := by
  funext i
  fin_cases i
  · show v 0 + 2 * (r : ℤ) * (z + w) 0
      = v 0 + 2 * (r : ℤ) * z 0 + 2 * (r : ℤ) * w 0
    show v 0 + 2 * (r : ℤ) * (z 0 + w 0)
      = v 0 + 2 * (r : ℤ) * z 0 + 2 * (r : ℤ) * w 0
    ring
  · show v 1 + 2 * (r : ℤ) * (z + w) 1
      = v 1 + 2 * (r : ℤ) * z 1 + 2 * (r : ℤ) * w 1
    show v 1 + 2 * (r : ℤ) * (z 1 + w 1)
      = v 1 + 2 * (r : ℤ) * z 1 + 2 * (r : ℤ) * w 1
    ring

/-- The good-block event only reads the field through the block. -/
theorem blockGood_congr (r : ℕ) (F G : Site 2 → ℝ) (ℓ : ℝ) (z z' : Site 2)
    (h : ∀ v : Site 2, F (blockShift r z v) = G (blockShift r z' v)) :
    BlockGood r F ℓ z ↔ BlockGood r G ℓ z' := by
  have e1 : (fun v : planeRectangle (2 * r) (2 * r) => F (blockShift r z (v : Site 2)))
      = fun v : planeRectangle (2 * r) (2 * r) => G (blockShift r z' (v : Site 2)) := by
    funext v; exact h _
  have e2 : (fun v : planeRectangle (4 * r) (2 * r) => F (blockShift r z (v : Site 2)))
      = fun v : planeRectangle (4 * r) (2 * r) => G (blockShift r z' (v : Site 2)) := by
    funext v; exact h _
  have e3 : (fun v : planeRectangle (2 * r) (4 * r) => F (blockShift r z (v : Site 2)))
      = fun v : planeRectangle (2 * r) (4 * r) => G (blockShift r z' (v : Site 2)) := by
    funext v; exact h _
  unfold BlockGood
  rw [e1, e2, e3]

/-- The finite-range block field of `lem:d4-finite-range-lower-bound`, read in
the coordinate plane. -/
def frBlockField (Aex : ℕ) (Aloc : ℝ) (R : ℕ) (ζ : Site 4 → ℝ) (u : Site 2) : ℝ :=
  frGreenFieldTime R (Aex * R ^ 2) ζ (planeEmbed u)
    + frExitValue Aex Aloc R ζ (planeEmbed u)

/-- `frBlockField` is shift-covariant: shifting the scenery `ζ` by `planeEmbed c` and reading
the field at `u` agrees with reading the unshifted field at `u + c`, from the shift covariance
of `frGreenFieldTime` and `frExitValue` together with the additivity `planeEmbed_add`. -/
theorem frBlockField_shift (Aex : ℕ) (Aloc : ℝ) (R : ℕ) (ζ : Site 4 → ℝ)
    (u c : Site 2) :
    frBlockField Aex Aloc R (shiftField (planeEmbed c) ζ) u
      = frBlockField Aex Aloc R ζ (u + c) := by
  unfold frBlockField
  rw [frGreenFieldTime_shiftField, frExitValue_shiftField, planeEmbed_add]

/-- Stationarity: the good block at `z + w` for the scenery is the good block at
`z` for the translated scenery. -/
theorem blockGood_frBlockField_shift (Aex : ℕ) (Aloc : ℝ) (R r : ℕ) (ℓ : ℝ)
    (ζ : Site 4 → ℝ) (z w : Site 2) :
    BlockGood r (frBlockField Aex Aloc R ζ) ℓ (z + w)
      ↔ BlockGood r
          (frBlockField Aex Aloc R
            (shiftField (planeEmbed ![2 * (r : ℤ) * w 0, 2 * (r : ℤ) * w 1]) ζ)) ℓ z := by
  refine blockGood_congr r _ _ ℓ (z + w) z fun v => ?_
  rw [frBlockField_shift, blockShift_add]

/-- The finite-time killed Green field `frGreenFieldTime r N ζ z` is measurable in the scenery
`ζ`, since it is a countable sum of the coordinate projections `ζ (z + u)` each scaled by a
constant kernel weight. -/
theorem measurable_frGreenFieldTime (r N : ℕ) (z : Site 4) :
    Measurable (fun ζ : Site 4 → ℝ => frGreenFieldTime r N ζ z) := by
  unfold frGreenFieldTime
  exact Measurable.tsum fun u => (measurable_pi_apply (z + u)).const_mul _

/-- The localized exit value `frExitValue Aex Aloc r ζ z` is measurable in the scenery `ζ`,
proved by rewriting it as `localizedExitAverage` at the explicit cubes `frCube z r` and
`frCube w (Aloc * r)`, using the indicator form `localizedExitPayoff_eq_indicator` and
`measurable_localizedExitAverage`. -/
theorem measurable_frExitValue (Aex : ℕ) (Aloc : ℝ) (r : ℕ) (z : Site 4) :
    Measurable (fun ζ : Site 4 → ℝ => frExitValue Aex Aloc r ζ z) := by
  have he : (fun ζ : Site 4 → ℝ => frExitValue Aex Aloc r ζ z)
      = fun ζ => localizedExitAverage (frCube z (r : ℝ)) (Aex * r ^ 2)
          (fun w => frCube w (Aloc * r)) (r ^ 2) ζ z := by
    funext ζ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun X =>
      (localizedExitPayoff_eq_indicator (frCube z (r : ℝ)) (Aex * r ^ 2)
        (fun w => frCube w (Aloc * r)) (r ^ 2) ζ X).symm
  rw [he]
  exact measurable_localizedExitAverage (by norm_num) _ _ _ _ _

/-- `frBlockField` is measurable in the scenery `ζ`, as the sum of the measurable Green field
`measurable_frGreenFieldTime` and exit value `measurable_frExitValue`. -/
theorem measurable_frBlockField (Aex : ℕ) (Aloc : ℝ) (R : ℕ) (u : Site 2) :
    Measurable (fun ζ : Site 4 → ℝ => frBlockField Aex Aloc R ζ u) :=
  (measurable_frGreenFieldTime R (Aex * R ^ 2) (planeEmbed u)).add
    (measurable_frExitValue Aex Aloc R (planeEmbed u))

/-- The good-block event `{ζ | BlockGood r (frBlockField Aex Aloc R ζ) ℓ z}` is measurable in
the scenery `ζ`, since `BlockGood` unfolds to a finite intersection of four crossing-threshold
conditions on `crossingValue`, each measurable because `crossingValue` is measurable in the
field and `frBlockField` is measurable in `ζ` by `measurable_frBlockField`. -/
theorem measurableSet_blockGood_frBlockField (Aex : ℕ) (Aloc : ℝ) (R r : ℕ) (ℓ : ℝ)
    (z : Site 2) :
    MeasurableSet {ζ : Site 4 → ℝ | BlockGood r (frBlockField Aex Aloc R ζ) ℓ z} := by
  have hm : ∀ (Q : Finset (Site 2)), IsLatticeRectangle Q → Q.Nonempty →
      Measurable (fun ζ : Site 4 → ℝ =>
        crossingValue Q (fun v : Q => frBlockField Aex Aloc R ζ (blockShift r z (v : Site 2)))) :=
    fun Q hQ hN => (measurable_crossingValue hQ hN).comp
      (measurable_pi_lambda _ fun v => measurable_frBlockField Aex Aloc R _)
  have h1 : MeasurableSet {ζ : Site 4 → ℝ | ℓ ≤ crossingValue (planeRectangle (2 * r) (2 * r))
      (fun v => frBlockField Aex Aloc R ζ (blockShift r z (v : Site 2)))} :=
    measurableSet_le measurable_const
      (hm _ (isLatticeRectangle_planeRectangle (2 * r) (2 * r))
        (planeRectangle_nonempty (2 * r) (2 * r)))
  have h2 : MeasurableSet {ζ : Site 4 → ℝ | ℓ ≤ crossingValue (planeRectangle (2 * r) (2 * r))
      (fun v => frBlockField Aex Aloc R ζ
        (blockShift r z ((transposeRectangle (2 * r) (2 * r) v : planeRectangle (2 * r) (2 * r)) :
          Site 2)))} :=
    measurableSet_le measurable_const
      ((measurable_crossingValue (isLatticeRectangle_planeRectangle (2 * r) (2 * r))
        (planeRectangle_nonempty (2 * r) (2 * r))).comp
        (measurable_pi_lambda _ fun v => measurable_frBlockField Aex Aloc R _))
  have h3 : MeasurableSet {ζ : Site 4 → ℝ | ℓ ≤ crossingValue (planeRectangle (4 * r) (2 * r))
      (fun v => frBlockField Aex Aloc R ζ (blockShift r z (v : Site 2)))} :=
    measurableSet_le measurable_const
      (hm _ (isLatticeRectangle_planeRectangle (4 * r) (2 * r))
        (planeRectangle_nonempty (4 * r) (2 * r)))
  have h4 : MeasurableSet {ζ : Site 4 → ℝ | ℓ ≤ crossingValue (planeRectangle (4 * r) (2 * r))
      (fun v => frBlockField Aex Aloc R ζ
        (blockShift r z ((transposeRectangle (4 * r) (2 * r) v : planeRectangle (2 * r) (4 * r)) :
          Site 2)))} :=
    measurableSet_le measurable_const
      ((measurable_crossingValue (isLatticeRectangle_planeRectangle (4 * r) (2 * r))
        (planeRectangle_nonempty (4 * r) (2 * r))).comp
        (measurable_pi_lambda _ fun v => measurable_frBlockField Aex Aloc R _))
  exact h1.inter (h2.inter (h3.inter h4))

/-- The Boolean indicator `ζ ↦ decide (BlockGood r (frBlockField Aex Aloc R ζ) ℓ z)` is
measurable, since its preimage of `{true}` is exactly the measurable set of
`measurableSet_blockGood_frBlockField`. -/
theorem measurable_decide_blockGood (Aex : ℕ) (Aloc : ℝ) (R r : ℕ) (ℓ : ℝ) (z : Site 2) :
    Measurable (fun ζ : Site 4 → ℝ => decide (BlockGood r (frBlockField Aex Aloc R ζ) ℓ z)) := by
  refine measurable_to_bool ?_
  have hpre : (fun ζ : Site 4 → ℝ => decide (BlockGood r (frBlockField Aex Aloc R ζ) ℓ z))
      ⁻¹' {true} = {ζ : Site 4 → ℝ | BlockGood r (frBlockField Aex Aloc R ζ) ℓ z} := by
    ext ζ
    simp
  rw [hpre]
  exact measurableSet_blockGood_frBlockField Aex Aloc R r ℓ z

/-- Stationarity of the good-block process under the i.i.d. scenery law. -/
theorem blockGood_law_stationary (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (Aex : ℕ) (Aloc : ℝ) (R r : ℕ) (ℓ : ℝ) (w : Site 2) :
    Measure.map
        (fun (ζ : Site 4 → ℝ) (z : Site 2) =>
          decide (BlockGood r (frBlockField Aex Aloc R ζ) ℓ (z + w))) (LatticeProb.iidLaw 4 ν)
      = Measure.map
        (fun (ζ : Site 4 → ℝ) (z : Site 2) =>
          decide (BlockGood r (frBlockField Aex Aloc R ζ) ℓ z)) (LatticeProb.iidLaw 4 ν) := by
  set y : Site 4 := planeEmbed ![2 * (r : ℤ) * w 0, 2 * (r : ℤ) * w 1] with hy
  have hmeasG : Measurable (fun (ζ : Site 4 → ℝ) (z : Site 2) =>
      decide (BlockGood r (frBlockField Aex Aloc R ζ) ℓ z)) :=
    measurable_pi_lambda _ fun z => measurable_decide_blockGood Aex Aloc R r ℓ z
  have hfun : (fun (ζ : Site 4 → ℝ) (z : Site 2) =>
        decide (BlockGood r (frBlockField Aex Aloc R ζ) ℓ (z + w)))
      = (fun (ζ : Site 4 → ℝ) (z : Site 2) =>
          decide (BlockGood r (frBlockField Aex Aloc R ζ) ℓ z)) ∘ shiftField y := by
    funext ζ z
    simp only [Function.comp_apply]
    exact decide_eq_decide.mpr (blockGood_frBlockField_shift Aex Aloc R r ℓ ζ z w)
  rw [hfun, ← Measure.map_map hmeasG (measurable_shiftField y)]
  congr 1
  exact massLaw_map_shiftField 4 ν y

end Sandpile
