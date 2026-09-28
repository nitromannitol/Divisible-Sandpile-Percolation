import Sandpile.Support.CrossFieldTilt

/-!
# Identifying the adaptive tilt with the Cameron--Martin shift

The identification of the adaptive tilt of `CrossStoppingSet` with the Cameron--Martin shift of
the white noise, and the level loss of Step 3 of `prop:fixed-scale-crossings` that follows
(`sandpile.tex:2334-2400`).

The tilt produced by the adaptive comparison is `a ∑ᵢ 𝒲(1_{Q_i}) - a²n/2`, one exponential
factor per revealed cube. For pairwise disjoint cubes of volume one the sum of the indicators
is the indicator of their union (`blockUnionInd_eq_sum`), whose `L²` norm squared is the
number of cubes (`integral_blockUnionInd_sq`, via `volume_blockUnion` and the idempotence
`blockUnionInd_mul_self`), so that tilt is exactly the Cameron--Martin tilt
`a 𝒲(k) - a²‖k‖²/2` of `CrossCameronMartin` at `k = 1_{⋃ Q_i}` (`cmLogDensity_univ_ae_eq`).
Combining the two gives the paper's Step 3 in the form the fixed-scale proposition consumes
(`cell_tilted_closedCrossEvent`): the crossing at a level exceeds the crossing at the level
raised by `a𝔪` by at most `|a|√(𝔼𝒩)/2`.
-/

open MeasureTheory ProbabilityTheory Set
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped NNReal ENNReal

namespace Sandpile.Support

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : (Space d → ℝ) → Ω → ℝ}

/-- The indicator of the union of the cubes the exploration can reveal: the paper's shifted
region (`sandpile.tex:2337-2341`). -/
noncomputable def blockUnionInd {ι : Type} (Q : ι → Set (Space d)) : Space d → ℝ :=
  Set.indicator (⋃ i, Q i) (fun _ => (1 : ℝ))

section Blocks

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Q : ι → Set (Space d))

omit [DecidableEq ι] in
/-- For pairwise disjoint sets, the indicator of their union is the sum of the individual
indicators, since exactly one term of the sum is nonzero at any point of the union and all
terms vanish off it. -/
theorem blockUnionInd_eq_sum (hQdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) (y : Space d) :
    blockUnionInd Q y = ∑ i : ι, Set.indicator (Q i) (fun _ => (1 : ℝ)) y := by
  classical
  by_cases hy : ∃ i, y ∈ Q i
  · obtain ⟨i₀, hi₀⟩ := hy
    have hle : blockUnionInd Q y = 1 :=
      Set.indicator_of_mem (Set.mem_iUnion.mpr ⟨i₀, hi₀⟩) (fun _ => (1 : ℝ))
    rw [hle, Finset.sum_eq_single i₀]
    · exact (Set.indicator_of_mem hi₀ (fun _ => (1 : ℝ))).symm
    · intro j _ hj
      refine Set.indicator_of_notMem (fun hmem => ?_) (fun _ => (1 : ℝ))
      exact Set.disjoint_left.mp (hQdisj j i₀ hj) hmem hi₀
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  · simp only [not_exists] at hy
    have hnot : y ∉ ⋃ i, Q i := by
      intro hmem
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
      exact hy i hi
    rw [blockUnionInd, Set.indicator_of_notMem hnot]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    exact Set.indicator_of_notMem (hy i) (fun _ => (1 : ℝ))

omit [Fintype ι] [DecidableEq ι] in
/-- `blockUnionInd` is a `{0,1}`-valued indicator, hence idempotent under multiplication. -/
theorem blockUnionInd_mul_self (y : Space d) :
    blockUnionInd Q y * blockUnionInd Q y = blockUnionInd Q y := by
  by_cases hy : y ∈ ⋃ i, Q i
  · rw [blockUnionInd, Set.indicator_of_mem hy]
    norm_num
  · rw [blockUnionInd, Set.indicator_of_notMem hy]
    norm_num

omit [DecidableEq ι] in
/-- The union of `Fintype.card ι` pairwise disjoint, measurable, unit-volume sets has volume
`Fintype.card ι`. -/
theorem volume_blockUnion (hQm : ∀ i, MeasurableSet (Q i)) (hQvol : ∀ i, volume (Q i) = 1)
    (hQdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) :
    volume (⋃ i, Q i) = (Fintype.card ι : ℝ≥0∞) := by
  rw [measure_iUnion (fun i j hij => hQdisj i j hij) hQm, tsum_fintype]
  simp [hQvol]

omit [DecidableEq ι] in
/-- `blockUnionInd` lies in `L²`, since it is the indicator of a measurable set of finite
volume (`volume_blockUnion`). -/
theorem memLp_blockUnionInd (hQm : ∀ i, MeasurableSet (Q i)) (hQvol : ∀ i, volume (Q i) = 1)
    (hQdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) :
    MemLp (blockUnionInd Q) 2 (volume : Measure (Space d)) := by
  refine memLp_indicator_const 2 (MeasurableSet.iUnion hQm) (1 : ℝ) (Or.inr ?_)
  rw [volume_blockUnion Q hQm hQvol hQdisj]
  exact ENNReal.natCast_ne_top _

omit [DecidableEq ι] in
/-- The squared `L²` norm of `blockUnionInd` is `Fintype.card ι`: idempotence
(`blockUnionInd_mul_self`) turns the square into the indicator itself, whose integral is the
volume of the union (`volume_blockUnion`). -/
theorem integral_blockUnionInd_sq (hQm : ∀ i, MeasurableSet (Q i))
    (hQvol : ∀ i, volume (Q i) = 1) (hQdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) :
    (∫ y : Space d, blockUnionInd Q y * blockUnionInd Q y) = (Fintype.card ι : ℝ) := by
  have hsq : (∫ y : Space d, blockUnionInd Q y * blockUnionInd Q y)
      = ∫ y : Space d, blockUnionInd Q y :=
    integral_congr_ae (Filter.Eventually.of_forall (blockUnionInd_mul_self Q))
  rw [hsq, blockUnionInd, integral_indicator_const _ (MeasurableSet.iUnion hQm),
    measureReal_def, volume_blockUnion Q hQm hQvol hQdisj]
  simp

end Blocks

/-- The adaptive tilt of `CrossStoppingSet` at pairwise disjoint cubes of volume one IS the
Cameron--Martin tilt of the white noise in the direction of the indicator of their union. -/
theorem cmLogDensity_univ_ae_eq (hW : IsWhiteNoise d W P) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : ι → Set (Space d)) (hQm : ∀ i, MeasurableSet (Q i)) (hQvol : ∀ i, volume (Q i) = 1)
    (hQdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) (a : ℝ) :
    cmLogDensity a (fun i => W (Set.indicator (Q i) (fun _ => (1 : ℝ))))
        (fun _ : Ω => (Finset.univ : Finset ι))
      =ᵐ[P] fun ω => a * W (blockUnionInd Q) ω
          - a ^ 2 * (∫ y : Space d, blockUnionInd Q y * blockUnionInd Q y) / 2 := by
  classical
  have hmem : ∀ i, MemLp (Set.indicator (Q i) (fun _ => (1 : ℝ))) 2
      (volume : Measure (Space d)) := fun i =>
    memLp_indicator_const 2 (hQm i) (1 : ℝ) (Or.inr (by rw [hQvol i]; exact ENNReal.one_ne_top))
  have hfun : blockUnionInd Q
      = ∑ i ∈ (Finset.univ : Finset ι), (1 : ℝ) • Set.indicator (Q i) (fun _ => (1 : ℝ)) := by
    funext y
    rw [blockUnionInd_eq_sum Q hQdisj y]
    simp
  have hsum := whiteNoise_finsetSum_ae W P hW (fun _ : ι => (1 : ℝ))
    (fun i => Set.indicator (Q i) (fun _ => (1 : ℝ))) hmem Finset.univ
  rw [← hfun] at hsum
  rw [integral_blockUnionInd_sq Q hQm hQvol hQdisj]
  filter_upwards [hsum] with ω hω
  simp only [cmLogDensity, Finset.card_univ]
  rw [hω]
  simp only [one_mul]
  ring

/-- **Step 3 of `prop:fixed-scale-crossings` at the level of the crossing events.**  The tilt
that the adaptive comparison produces moves the crossing at level `l` to the crossing at level
`l - a𝔪`. -/
theorem cell_tilted_closedCrossEvent (hd : d = 2 ∨ d = 3) (hW : IsWhiteNoise d W P)
    {ι : Type} [Fintype ι] [DecidableEq ι] (Q : ι → Set (Space d))
    (hQm : ∀ i, MeasurableSet (Q i)) (hQvol : ∀ i, volume (Q i) = 1)
    (hQdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j)) (hcard : 0 < Fintype.card ι)
    (a m : ℝ) (aa bb : Fin 2 → ℝ) (dir : Fin 2) (l : ℝ)
    (hmass : ∀ u ∈ rectSet aa bb,
      (∫ y : Space d, ballKernel d 1 u y * blockUnionInd Q y) = m) :
    (P.tilted (cmLogDensity a (fun i => W (Set.indicator (Q i) (fun _ => (1 : ℝ))))
        (fun _ : Ω => (Finset.univ : Finset ι))))
        (closedCrossEvent (ballField d W 1) aa bb dir l)
      = P (closedCrossEvent (ballField d W 1) aa bb dir (l - a * m)) := by
  have hv : 0 < ∫ y : Space d, blockUnionInd Q y * blockUnionInd Q y := by
    rw [integral_blockUnionInd_sq Q hQm hQvol hQdisj]
    exact_mod_cast hcard
  rw [tilted_congr (cmLogDensity_univ_ae_eq hW Q hQm hQvol hQdisj a)]
  exact whiteNoise_tilted_closedCrossEvent hd hW
    (memLp_blockUnionInd Q hQm hQvol hQdisj) hv a m aa bb dir l hmass

end Sandpile.Support
