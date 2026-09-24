/-
Steps 2 and 3 of `prop:fixed-scale-crossings` (`sandpile.tex:2248-2400`) assembled: from an
adaptive exploration of the unit cells with a subquadratic expected count, the level loss the
proposition needs.

The exploration enters only through three properties, all of them in the vocabulary of
`CrossStoppingSet`:

* `IsIndepStoppingSet`: the rule reveals a cell on the strength of the cells already revealed
  (`sandpile.tex:2354-2360`);
* `IndepBlockDecides`: when it stops, the revealed cells decide the crossing
  (`sandpile.tex:2390`);
* `∫ (S ω).card ∂P ≤ Cn R^{2-α₁}`: the subquadratic count (`sandpile.tex:2288-2296`);

together with the geometric fact that the union of the cells it can reveal contains the
support of every unit kernel the crossing evaluates, so that the shift raises every field
value of the rectangle by the same amount `a𝔪` (`sandpile.tex:2337-2345`).

Everything else - the adaptive Cameron--Martin identity, Pinsker, the identification of the
tilt with the shift, and the passage from the measurable representative of the crossing to the
crossing itself - is proved.
-/
import Sandpile.Support.CrossCellShift
import Sandpile.Support.CrossLevelLoss

open MeasureTheory ProbabilityTheory Set
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped NNReal ENNReal

namespace Sandpile.Support

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : (Space d → ℝ) → Ω → ℝ}

/-- The level loss from an adaptive cell exploration, in the raw form: the crossing at the
level lowered by `a𝔪` exceeds the crossing at the level by at most `|a|√N/2`. -/
theorem cross_level_loss_of_cell_exploration (hPin : Sandpile.External.Pinsker)
    (hd : d = 2 ∨ d = 3) (hW : IsWhiteNoise d W P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun x => ballField d W 1 x ω)
    {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → Sandpile.Site d)
    (hz : Function.Injective z) (hcard : 0 < Fintype.card ι)
    {S : Ω → Finset ι}
    (hS : IsIndepStoppingSet (fun i => noiseBlockAlg W (cell d 1 (z i))) S)
    (a N m l : ℝ) (hN : ∫ ω, ((S ω).card : ℝ) ∂P ≤ N)
    (aa bb : Fin 2 → ℝ) (hab : ∀ j, aa j < bb j) (dir : Fin 2)
    (hE : IndepBlockDecides (fun i => noiseBlockAlg W (cell d 1 (z i))) S
      (closedCrossEvent (ballField d W 1) aa bb dir l))
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
  have hae1 : closedCrossEvent (ballField d W 1) aa bb dir (l - a * m)
      =ᵐ[P] {ω | Crosses aa bb dir {x | l - a * m ≤ ballField d W 1 x ω}} :=
    closedCrossEvent_ae_eq P _ aa bb dir hab _ hcont
  have hae2 : closedCrossEvent (ballField d W 1) aa bb dir l
      =ᵐ[P] {ω | Crosses aa bb dir {x | l ≤ ballField d W 1 x ω}} :=
    closedCrossEvent_ae_eq P _ aa bb dir hab _ hcont
  rw [← measure_congr hae1, ← measure_congr hae2,
    ← cell_tilted_closedCrossEvent hd hW (fun i => cell d 1 (z i)) hQm hQvol hQdisj hcard
      a m aa bb dir l hmass]
  exact whiteNoise_cell_level_loss hPin hW z hz hS a N hN hE

/-- The level loss of `prop:fixed-scale-crossings` at one scale, in the shape the proposition
consumes: at level `L/R`, with the count `Cn R^{2-α₁}`, the crossing at level zero exceeds the
crossing at level `L/R` by at most `(√Cn/(2𝔪)) L R^{-α₁/2}` (`sandpile.tex:2392-2398`). -/
theorem cross_zero_level_loss_of_cell_exploration (hPin : Sandpile.External.Pinsker)
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
    (hE : IndepBlockDecides (fun i => noiseBlockAlg W (cell d 1 (z i))) S
      (closedCrossEvent (ballField d W 1) aa bb dir (L / R)))
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
  have hbase := cross_level_loss_of_cell_exploration hPin hd hW hcont z hz hcard hS
    (L / (m * R)) N m (L / R) hN aa bb hab dir hE hmass
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

end Sandpile.Support
