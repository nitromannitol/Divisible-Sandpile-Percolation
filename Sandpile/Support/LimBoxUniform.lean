/-
From small moments to a small supremum on a box.

`LatticeProb.kolmogorovBoundPi` (the library's quantitative Kolmogorov-Chentsov
boundedness theorem) turns a `p`-th moment
Hölder bound with constant `M` on a box of dimension `k < q`, together with a moment
bound at the box's corner, into an explicit level `B` which the field does not exceed
anywhere on the box, off an event of probability at most a prescribed `ε`.

The level `B` it produces does not tend to zero with `M`; what does is the field
itself, and rescaling converts one into the other.  Applying the theorem to `X/η`
with `η` chosen so that `η·B ≤ c` gives: there is a THRESHOLD `M₀ > 0`, depending
only on the box, the exponents, the level `c` and the probability `ε`, such that any
field whose two moment bounds are below `M₀` stays below `c` on the whole box off an
event of probability at most `ε`.  That is the shape the crossing argument needs,
since the moment bounds of the difference field tend to zero with the horizon.
-/
import LatticeProb.Prob.KolmogorovBound
import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- **A threshold on the moments which forces a small supremum on the box.** -/
theorem exists_moment_threshold {k : ℕ} (a b : Fin k → ℝ) (p q : ℝ) (hp : 0 < p)
    (hq : (k : ℝ) < q) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₀ : ℝ, 0 < M₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ X : (Fin k → ℝ) → Ω → ℝ,
          (∀ u, Measurable (X u)) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            Integrable (fun ω => |X u ω - X v ω| ^ p) P) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M₀ * dist u v ^ q) →
          Integrable (fun ω => |X a ω| ^ p) P →
          (∫ ω, |X a ω| ^ p ∂P ≤ M₀) →
          (∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b)) →
          P {ω | ∃ u ∈ Set.Icc a b, c < |X u ω|} ≤ ENNReal.ofReal ε := by
  obtain ⟨B, hB⟩ := LatticeProb.kolmogorovBoundPi k a b p q 1 hp hq ε hε
  set B' : ℝ := max B 1 with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set η : ℝ := c / B' with hη
  have hηpos : 0 < η := div_pos hc hB'pos
  refine ⟨η ^ p, Real.rpow_pos_of_pos hηpos p, ?_⟩
  intro Ω _ P hP X hXm hint hbound hu0int hu0bound hcont
  -- the rescaled field
  set Y : (Fin k → ℝ) → Ω → ℝ := fun u ω => X u ω / η with hY
  have hYm : ∀ u, Measurable (Y u) := fun u => (hXm u).div_const η
  have habs : ∀ (u v : Fin k → ℝ) (ω : Ω), |Y u ω - Y v ω| ^ p
      = |X u ω - X v ω| ^ p / η ^ p := by
    intro u v ω
    rw [hY]
    have hsub : X u ω / η - X v ω / η = (X u ω - X v ω) / η := by ring
    rw [hsub, abs_div, abs_of_pos hηpos, Real.div_rpow (abs_nonneg _) hηpos.le]
  have habs0 : ∀ (u : Fin k → ℝ) (ω : Ω), |Y u ω| ^ p = |X u ω| ^ p / η ^ p := by
    intro u ω
    rw [hY, abs_div, abs_of_pos hηpos, Real.div_rpow (abs_nonneg _) hηpos.le]
  have hYint : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      Integrable (fun ω => |Y u ω - Y v ω| ^ p) P := by
    intro u hu v hv
    refine ((hint u hu v hv).div_const (η ^ p)).congr ?_
    filter_upwards with ω
    rw [habs u v ω]
  have hYbound : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      ∫ ω, |Y u ω - Y v ω| ^ p ∂P ≤ 1 * dist u v ^ q := by
    intro u hu v hv
    have hrw : (∫ ω, |Y u ω - Y v ω| ^ p ∂P) = (∫ ω, |X u ω - X v ω| ^ p ∂P) / η ^ p := by
      rw [← integral_div]
      exact integral_congr_ae (Eventually.of_forall fun ω => habs u v ω)
    rw [hrw, one_mul, div_le_iff₀ (Real.rpow_pos_of_pos hηpos p)]
    calc (∫ ω, |X u ω - X v ω| ^ p ∂P) ≤ η ^ p * dist u v ^ q := hbound u hu v hv
      _ = dist u v ^ q * η ^ p := by ring
  have hY0int : Integrable (fun ω => |Y a ω| ^ p) P := by
    refine (hu0int.div_const (η ^ p)).congr ?_
    filter_upwards with ω
    rw [habs0 a ω]
  have hY0bound : (∫ ω, |Y a ω| ^ p ∂P) ≤ 1 := by
    have hrw : (∫ ω, |Y a ω| ^ p ∂P) = (∫ ω, |X a ω| ^ p ∂P) / η ^ p := by
      rw [← integral_div]
      exact integral_congr_ae (Eventually.of_forall fun ω => habs0 a ω)
    rw [hrw, div_le_one (Real.rpow_pos_of_pos hηpos p)]
    exact hu0bound
  have hYcont : ∀ ω, ContinuousOn (fun u => Y u ω) (Set.Icc a b) := by
    intro ω
    exact (hcont ω).div_const η
  have hmain := hB P hP Y hYm hYint hYbound hY0int hY0bound hYcont
  refine le_trans (measure_mono ?_) hmain
  rintro ω ⟨u, hu, hlt⟩
  refine ⟨u, hu, ?_⟩
  have hBB' : B ≤ B' := le_max_left _ _
  have hηB : η * B ≤ c := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ hB'pos]
    nlinarith [hc.le, hB'pos]
  have hYval : |Y u ω| = |X u ω| / η := by
    rw [hY, abs_div, abs_of_pos hηpos]
  rw [hYval, lt_div_iff₀ hηpos]
  calc B * η = η * B := by ring
    _ ≤ c := hηB
    _ < |X u ω| := hlt

end Sandpile.Support
