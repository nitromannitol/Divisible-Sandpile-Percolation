/- Tested L² linearization along the scale sequences of the many-limits construction. -/
import Sandpile.Support.LinJacobianFirstConjunct
import Sandpile.Support.Dgt4APathSurvivalSequence
import Sandpile.Support.Dgt4ABandSequence

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile.Support
open Sandpile
variable {d : ℕ}

/-- The tested linearization estimate along any strictly increasing sequence of
scales tending to infinity. Survival and covariance are assumed only on that sequence. -/
theorem dgt4_tested_linearization_sequence [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmean : ∫ z, z ∂ν = 0) (hsqν : Integrable (fun z => z ^ 2) ν)
    (φ : Space d → ℝ) (hφtest : Sandpile.Continuum.IsTestFn Set.univ φ)
    (Rseq : ℕ → ℝ) (hRmono : StrictMono Rseq) (hRtop : Tendsto Rseq atTop atTop)
    (T : ℝ) (hT : 0 < T) (q : ℕ → ℕ → ℝ) (C : ℝ)
    (hsurv : Tendsto (fun k : ℕ => ((Rseq k) ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊(Rseq k) ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, survivalInd σ ⌊(Rseq k) ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) - q k j|
            ∂(walkLaw d 0)) atTop (𝓝 0))
    (hcov : ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℕ → ℝ, (∀ k : ℕ, 0 ≤ εfun k) ∧ Tendsto εfun atTop (𝓝 0) ∧
        ∀ k : ℕ, ∀ i j : ℕ,
          (i : ℝ) ≤ ((⌊(Rseq k) ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * (Rseq k) ^ 2 →
          (j : ℝ) ≤ ((⌊(Rseq k) ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * (Rseq k) ^ 2 →
          ∀ X Y : ℕ → Site d,
            Frozen.DGT4PathSurvival.IsNNPath i X →
            Frozen.DGT4PathSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.survivalInd σ ⌊(Rseq k) ^ 2 * T⌋₊ i X *
                  Sandpile.survivalInd σ ⌊(Rseq k) ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.survivalInd σ ⌊(Rseq k) ^ 2 * T⌋₊ i X
                  ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.survivalInd σ ⌊(Rseq k) ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * (Rseq k) ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun k) :
    Tendsto (fun k : ℕ =>
        ∫ σ, ((Rseq k) ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing (Rseq k)
          (fun x => Sandpile.odometer σ ⌊(Rseq k) ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊(Rseq k) ^ 2 * T⌋₊ -
            ∑ j ∈ Finset.range ⌊(Rseq k) ^ 2 * T⌋₊,
              q k j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0) := by
  classical
  let index : ℝ → ℕ := Function.invFun Rseq
  have hindex : ∀ k, index (Rseq k) = k := Function.leftInverse_invFun hRmono.injective
  let l : Filter ℝ := Filter.map Rseq atTop
  let qext : ℝ → ℕ → ℝ := fun R => q (index R)
  have hsurv' : Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, survivalInd σ ⌊R ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) - qext R j|
            ∂(walkLaw d 0)) l (𝓝 0) := by
    change Tendsto _ (Filter.map Rseq atTop) _
    rw [Filter.tendsto_map'_iff]
    simpa only [Function.comp_def, qext, hindex] using hsurv
  have hcov' : ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun l (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
          (j : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Site d,
            Frozen.DGT4PathSurvival.IsNNPath i X →
            Frozen.DGT4PathSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ i X *
                  Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ i X
                  ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν))| ≤
              max C 0 / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R := by
    intro δ hδ
    obtain ⟨εfun, hε0, hεlim, hε⟩ := hcov δ hδ
    let ext : ℝ → ℝ := fun R => if R ∈ Set.range Rseq then εfun (index R) else 1
    have hext : ∀ k, ext (Rseq k) = εfun k := by
      intro k
      simp only [ext, Set.mem_range_self, if_true, hindex]
    refine ⟨ext, ?_, ?_, ?_⟩
    · intro R
      dsimp [ext]
      split_ifs
      · exact hε0 _
      · norm_num
    · change Tendsto ext (Filter.map Rseq atTop) _
      rw [Filter.tendsto_map'_iff]
      simpa only [Function.comp_def, hext] using hεlim
    · intro R i j hi hj X Y hX hY
      have hsum : 0 ≤ ∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
          Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Set.indicator_nonneg (fun _ _ => zero_le_one) _
      have hden : 0 ≤ δ * R ^ 2 := mul_nonneg hδ.1.le (sq_nonneg R)
      by_cases hR : R ∈ Set.range Rseq
      · obtain ⟨k, rfl⟩ := hR
        rw [hext]
        refine (hε k i j hi hj X Y hX hY).trans ?_
        exact add_le_add
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left C 0) hden) hsum) le_rfl
      · have hone := abs_cov_survival_le_one ν ⌊R ^ 2 * T⌋₊ i j X Y
        change |_ - _ * _| ≤ _ at hone
        refine hone.trans ?_
        rw [show ext R = 1 from if_neg hR]
        exact le_add_of_nonneg_left (mul_nonneg (div_nonneg (le_max_right C 0) hden) hsum)
  have h := tendsto_l2_frozen_pairing hd hGreen hInter ν hmean hsqν φ hφtest T hT
    qext (max C 0) hsurv' hcov' hRtop
  simpa only [Function.comp_def, qext, hindex] using h.comp (tendsto_map (f := Rseq) (x := atTop))

/-- Independent contact thresholds on the chosen scales imply the tested
linearization with weight `(1-j/(R²T))^κ` on precisely those scales. -/
theorem dgt4_tested_linearization_of_thresholds_sequence
    (d : ℕ) (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (Rseq : ℕ → ℝ) (hRmono : StrictMono Rseq) (hRtop : Tendsto Rseq atTop atTop)
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : UniformContactThresholdsAlong d ν κ T Rseq)
    (φ : Space d → ℝ) (hφ : IsTestFn Set.univ φ) :
    Tendsto (fun k : ℕ =>
        ∫ σ, ((Rseq k) ^ (((d : ℝ) - 4) / 2) * latticePairing (Rseq k)
          (fun x => odometer σ ⌊(Rseq k) ^ 2 * T⌋₊ x -
            meanOdometer (centeredMassLaw d ν) ⌊(Rseq k) ^ 2 * T⌋₊ -
            ∑ j ∈ Finset.range ⌊(Rseq k) ^ 2 * T⌋₊,
              (1 - (j : ℝ) / ((Rseq k) ^ 2 * T)) ^ κ *
                (avg^[j] (scenery d σ)) x) φ) ^ 2
          ∂(centeredMassLaw d ν)) atTop (𝓝 0) := by
  haveI : NeZero d := ⟨by omega⟩
  have hsq : Integrable (fun z : ℝ => z ^ 2) ν :=
    ((evariance_lt_top_iff_memLp aestronglyMeasurable_id).mp hvar').integrable_sq
  obtain ⟨hsurv, C, hcov⟩ := dgt4_path_survival_sequence_indep d hd ν hvar'
    (fun σ x => -(green d 0 0 * scenery d σ x)) (fun _ _ => rfl)
    Rseq hRtop T hT κ hκ hthresholds
  exact dgt4_tested_linearization_sequence hd hGreen hInter ν hmean
    hsq φ hφ Rseq hRmono hRtop T hT
    (fun k j => (1 - (j : ℝ) / ((Rseq k) ^ 2 * T)) ^ κ) C hsurv hcov

end Sandpile.Support
