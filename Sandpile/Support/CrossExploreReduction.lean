/-
`prop:fixed-scale-crossings` (`sandpile.tex:2119-2135`) reduced to the exploration of Step 2
alone.

Everything the proposition needs except the construction of the exploration rule is proved:
Step 1 is `uniform_ballField_zero_crossing` (from RSW and Pitt), Step 3 is the adaptive
Cameron--Martin comparison of `CrossStoppingSet` together with the shift identity of
`CrossCellShift`, and the arithmetic is `CrossLevelLoss`.  What is left is the hypothesis
`hexp` below: at every model and every scale, a rule which reveals the unit cells one at a
time on the strength of the cells already revealed, decides the crossing when it stops, reveals
`Cn R^{2-α₁}` cells in expectation, and can reveal every cell meeting the unit ball about a
point of the rectangle.  `CrossExploreRec` builds such rules from a recursion and proves the
first of these clauses from the recursion's own measurability.
-/
import Sandpile.Support.CrossExploreLoss
import Sandpile.Support.CrossFieldVersion
import Sandpile.Support.CrossFixedScaleZero

open MeasureTheory ProbabilityTheory Set Filter
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- The rectangle of the proposition is nondegenerate at every admissible scale. -/
theorem crossing_rect_lt {θ R : ℝ} (hθ : 0 < θ) (hR : max 1 θ⁻¹ ≤ R) (j : Fin 2) :
    (![-(θ * R), 0] : Fin 2 → ℝ) j < (![θ * R, 2 * R] : Fin 2 → ℝ) j := by
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  fin_cases j
  · show -(θ * R) < θ * R
    nlinarith
  · show (0 : ℝ) < 2 * R
    linarith

/-- The mass condition of the shift from the geometric covering condition: if every cell
meeting the unit ball about `u` can be revealed, the shift raises the field at `u` by the full
mass of the unit kernel. -/
theorem mass_of_covering {d : ℕ} {ι : Type} (z : ι → Sandpile.Site d) (u : Space 2)
    (hcov : ∀ y : Space d, ‖(planePoint (d := d) u) - y‖ < 1 → y ∈ ⋃ i, cell d 1 (z i)) :
    (∫ y : Space d, ballKernel d 1 u y * blockUnionInd (fun i => cell d 1 (z i)) y)
      = ∫ y : Space d, centredKernel d 1 y := by
  rw [blockUnionInd, integral_ballKernel_mul_indicator_of_covers u _ hcov,
    integral_ballKernel_eq_centred]

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : (Space d → ℝ) → Ω → ℝ}

/-- The level loss when the exploration decides the crossing of a VERSION of the field: the
white noise is only almost surely additive over a decomposition of a test function, so the
field an exploration computes from the cells it has revealed agrees with `ballField` only
almost surely at each point.  The crossing events of the two fields differ by a null set, and
the tilt is absolutely continuous with respect to `P`, so the level loss is unchanged. -/
theorem cross_level_loss_of_cell_exploration_version (hPin : Sandpile.External.Pinsker)
    (hd : d = 2 ∨ d = 3) (hW : IsWhiteNoise d W P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun x => ballField d W 1 x ω)
    {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → Sandpile.Site d)
    (hz : Function.Injective z) (hcard : 0 < Fintype.card ι)
    {S : Ω → Finset ι}
    (hS : IsIndepStoppingSet (fun i => noiseBlockAlg W (cell d 1 (z i))) S)
    (a N m l : ℝ) (hN : ∫ ω, ((S ω).card : ℝ) ∂P ≤ N)
    (aa bb : Fin 2 → ℝ) (hab : ∀ j, aa j < bb j) (dir : Fin 2)
    (X : Space 2 → Ω → ℝ) (hX : ∀ u, X u =ᵐ[P] ballField d W 1 u)
    (hE : IndepBlockDecides (fun i => noiseBlockAlg W (cell d 1 (z i))) S
      (closedCrossEvent X aa bb dir l))
    (hmass : ∀ u ∈ rectSet aa bb,
      (∫ y : Space d, ballKernel d 1 u y * blockUnionInd (fun i => cell d 1 (z i)) y) = m) :
    P {ω | Crosses aa bb dir {x | l - a * m ≤ ballField d W 1 x ω}}
      ≤ P {ω | Crosses aa bb dir {x | l ≤ ballField d W 1 x ω}}
        + ENNReal.ofReal (|a| / 2 * Real.sqrt N) := by
  have hQm : ∀ i, MeasurableSet (cell d 1 (z i)) := fun i => measurableSet_cell d 1 (z i)
  have hQvol : ∀ i, volume (cell d 1 (z i)) = 1 := fun i => by
    simpa using volume_cell d one_pos (z i)
  have hQdisj : ∀ i j, i ≠ j → Disjoint (cell d 1 (z i)) (cell d 1 (z j)) :=
    fun i j hij => cell_disjoint (fun h => hij (hz h))
  have hac : P.tilted (cmLogDensity a
      (fun i => W (Set.indicator (cell d 1 (z i)) (fun _ => (1 : ℝ))))
      (fun _ : Ω => (Finset.univ : Finset ι))) ≪ P := tilted_absolutelyContinuous P _
  have hae1 : closedCrossEvent (ballField d W 1) aa bb dir (l - a * m)
      =ᵐ[P] {ω | Crosses aa bb dir {x | l - a * m ≤ ballField d W 1 x ω}} :=
    closedCrossEvent_ae_eq P _ aa bb dir hab _ hcont
  have hae2 : closedCrossEvent (ballField d W 1) aa bb dir l
      =ᵐ[P] {ω | Crosses aa bb dir {x | l ≤ ballField d W 1 x ω}} :=
    closedCrossEvent_ae_eq P _ aa bb dir hab _ hcont
  have h1 := measure_closedCrossEvent_eq_of_field_ae P _ hac (ballField d W 1) X
    (fun u => (hX u).symm) aa bb dir l
  have h2 := measure_closedCrossEvent_eq_of_field_ae P P (Measure.AbsolutelyContinuous.refl P)
    X (ballField d W 1) hX aa bb dir l
  have h3 := cell_tilted_closedCrossEvent hd hW (fun i => cell d 1 (z i)) hQm hQvol hQdisj hcard
    a m aa bb dir l hmass
  have h4 := whiteNoise_cell_level_loss hPin hW z hz hS a N hN hE
  rw [← measure_congr hae1, ← measure_congr hae2, ← h3, h1, ← h2]
  exact h4

/-- The level loss at level `L/R`, for a version of the field, with the constant of
`sandpile.tex:2392-2398`. -/
theorem cross_zero_level_loss_of_cell_exploration_version (hPin : Sandpile.External.Pinsker)
    (hd : d = 2 ∨ d = 3) (hW : IsWhiteNoise d W P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun x => ballField d W 1 x ω)
    {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → Sandpile.Site d)
    (hz : Function.Injective z) (hcard : 0 < Fintype.card ι)
    {S : Ω → Finset ι}
    (hS : IsIndepStoppingSet (fun i => noiseBlockAlg W (cell d 1 (z i))) S)
    (m L R N Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hCn : 0 ≤ Cn) (hNb : N ≤ Cn * R ^ (2 - α₁))
    (hN : ∫ ω, ((S ω).card : ℝ) ∂P ≤ N)
    (aa bb : Fin 2 → ℝ) (hab : ∀ j, aa j < bb j) (dir : Fin 2)
    (X : Space 2 → Ω → ℝ) (hX : ∀ u, X u =ᵐ[P] ballField d W 1 u)
    (hE : IndepBlockDecides (fun i => noiseBlockAlg W (cell d 1 (z i))) S
      (closedCrossEvent X aa bb dir (L / R)))
    (hmass : ∀ u ∈ rectSet aa bb,
      (∫ y : Space d, ballKernel d 1 u y * blockUnionInd (fun i => cell d 1 (z i)) y) = m) :
    P {ω | Crosses aa bb dir {x | 0 ≤ ballField d W 1 x ω}}
      ≤ P {ω | Crosses aa bb dir {x | L / R ≤ ballField d W 1 x ω}}
        + ENNReal.ofReal (Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2))) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hRne : R ≠ 0 := ne_of_gt hR0
  have hshift : L / R - L / (m * R) * m = 0 := by
    field_simp
    ring
  have hbase := cross_level_loss_of_cell_exploration_version hPin hd hW hcont z hz hcard hS
    (L / (m * R)) N m (L / R) hN aa bb hab dir X hX hE hmass
  rw [hshift] at hbase
  refine le_trans hbase (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have habs : |L / (m * R)| = L / (m * R) := abs_of_nonneg (by positivity)
  rw [habs]
  have hfac : (0 : ℝ) ≤ L / (m * R) / 2 := by positivity
  have hcount : L / (m * R) / 2 * Real.sqrt N
      ≤ L / (m * R) / 2 * (Real.sqrt Cn * R ^ (1 - α₁ / 2)) :=
    mul_le_mul_of_nonneg_left (sqrt_count_bound hR hCn hNb) hfac
  have hRsplit : R ^ (1 - α₁ / 2) = R * R ^ (-(α₁ / 2)) := by
    calc R ^ (1 - α₁ / 2) = R ^ ((1 : ℝ) + -(α₁ / 2)) := by rw [sub_eq_add_neg]
      _ = R ^ (1 : ℝ) * R ^ (-(α₁ / 2)) := Real.rpow_add hR0 1 (-(α₁ / 2))
      _ = R * R ^ (-(α₁ / 2)) := by rw [Real.rpow_one]
  have hcancel : L / (m * R) / 2 * (Real.sqrt Cn * (R * R ^ (-(α₁ / 2))))
      = Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2)) := by
    field_simp
  rw [hRsplit, hcancel] at hcount
  exact hcount

/-- **`prop:fixed-scale-crossings` from the exploration of Step 2.**  The only hypothesis that
is not proved in the repository is `hexp`, the existence of the paper's exploration rule at
every model and every scale. -/
theorem fixed_scale_crossings_of_cell_exploration
    (hRSW : Sandpile.External.ContinuumRSW) (hPitt : Sandpile.External.PittGaussianFKG)
    (hPin : Sandpile.External.Pinsker)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ) (Cn α₁ : ℝ)
    (hCn : 0 ≤ Cn) (hα₁ : 0 < α₁)
    (hexp : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P, Continuous fun x => ballField d W s x ω) →
        ∀ L : ℝ, 0 < L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
        ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (z : ι → Sandpile.Site d)
          (S : Ω → Finset ι) (X : Space 2 → Ω → ℝ),
          Function.Injective z ∧ 0 < Fintype.card ι ∧
          IsIndepStoppingSet (fun i => noiseBlockAlg W (cell d 1 (z i))) S ∧
          (∫ ω, ((S ω).card : ℝ) ∂P) ≤ Cn * R ^ (2 - α₁) ∧
          (∀ u : Space 2, X u =ᵐ[P] ballField d W 1 u) ∧
          IndepBlockDecides (fun i => noiseBlockAlg W (cell d 1 (z i))) S
            (closedCrossEvent X ![-(θ * R), 0] ![θ * R, 2 * R] 0 (L / R)) ∧
          (∀ u ∈ rectSet ![-(θ * R), 0] ![θ * R, 2 * R],
            ∀ y : Space d, ‖(planePoint (d := d) u) - y‖ < 1 →
              y ∈ ⋃ i, cell d 1 (z i))) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P, Continuous fun x => ballField d W s x ω) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {x | L / R ≤ ballField d W 1 x ω}}) atTop := by
  refine fixed_scale_crossings_of_zero_level_loss hRSW hPitt d hd θ hθ
    (Real.sqrt Cn / (2 * ∫ y : Space d, centredKernel d 1 y)) (α₁ / 2) (by positivity) ?_
  have hmass : 0 < ∫ y : Space d, centredKernel d 1 y := centredKernel_mass_pos hd
  intro Ω _ P _ W hW hcont L hL R hR
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · subst hL0
    simp
  obtain ⟨ι, hfin, hdec, z, S, X, hz, hcard, hS, hN, hX, hE, hcov⟩ :=
    hexp Ω P W hW hcont L hLpos R hR
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
  exact cross_zero_level_loss_of_cell_exploration_version hPin hd hW (hcont 1 one_pos le_rfl) z hz hcard
    hS _ L R (Cn * R ^ (2 - α₁)) Cn α₁ hmass hL hR1 hCn le_rfl hN
    ![-(θ * R), 0] ![θ * R, 2 * R] (crossing_rect_lt hθ hR) 0 X hX hE
    (fun u hu => mass_of_covering z u (hcov u hu))

end Sandpile.Support
