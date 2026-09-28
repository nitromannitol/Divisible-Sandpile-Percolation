import Sandpile.Support.LinStep3Core
import Sandpile.Frozen.DGT4PathSurvival

/-!
The sequence-indexed independent-threshold form of `lem:dgt4-path-survival`
(`sandpile.tex:5469-5486`), used in Step 3 of `thm:dgt4-many-limits`.
The contact thresholds and both conclusions are required only along `Rseq`.
The threshold field is `-G(0,0)ζ`, so its factorization is exact.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile

/-- Averaged survival and the covariance bound along diverging scales for the
independent threshold field in the many-limits construction. -/
theorem dgt4_path_survival_sequence_indep
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ)
    (hJ : ∀ σ x, J σ x = -(Sandpile.green d 0 0 * Sandpile.scenery d σ x))
    (Rseq : ℕ → ℝ) (hRtop : Tendsto Rseq atTop atTop)
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ k : ℕ in atTop, ∀ m : ℕ, ⌈ε * (⌊(Rseq k) ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊(Rseq k) ^ 2 * T⌋₊ →
        |(m : ℝ) * ((Sandpile.centeredMassLaw d ν)
              {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (Sandpile.green d 0 0 * κ) - 1| +
          (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
            (symmDiff {σ | Sandpile.odometer σ m 0 = 0}
              {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
                J σ 0})).toReal ≤ η) :
    Tendsto (fun k : ℕ => ((Rseq k) ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊(Rseq k) ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊(Rseq k) ^ 2 * T⌋₊ j X
                ∂(Sandpile.centeredMassLaw d ν)) -
              (1 - (j : ℝ) / ((Rseq k) ^ 2 * T)) ^ κ| ∂(Sandpile.walkLaw d 0))
      atTop (𝓝 0) ∧
    ∃ C : ℝ, ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℕ → ℝ, (∀ k : ℕ, 0 ≤ εfun k) ∧ Tendsto εfun atTop (𝓝 0) ∧
        ∀ k : ℕ, ∀ i j : ℕ,
          (i : ℝ) ≤ (⌊(Rseq k) ^ 2 * T⌋₊ : ℝ) - δ * (Rseq k) ^ 2 →
            (j : ℝ) ≤ (⌊(Rseq k) ^ 2 * T⌋₊ : ℝ) - δ * (Rseq k) ^ 2 →
          ∀ X Y : ℕ → Sandpile.Site d,
            Sandpile.Frozen.DGT4PathSurvival.IsNNPath i X →
            Sandpile.Frozen.DGT4PathSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊(Rseq k) ^ 2 * T⌋₊ i X *
                  Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊(Rseq k) ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊(Rseq k) ^ 2 * T⌋₊ i X
                  ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊(Rseq k) ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * (Rseq k) ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun k := by
  haveI : NeZero d := ⟨by omega⟩
  let l : Filter ℝ := Filter.map Rseq atTop
  have hl : l ≤ atTop := hRtop
  have hscale : Tendsto Rseq atTop l := tendsto_map
  have hthresholds' : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in l, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal ≤ η :=
    hthresholds
  have hshift := fun t b y => measure_threshold_symmDiff_shift ν J hJ t b y
  have hnull := fun b => nullMeasurableSet_threshold_indep ν J hJ 0 b
  have hfact : ∀ theta : ℝ, 0 < theta → ∀ K : ℝ, 1 ≤ K →
      ∀ᶠ R : ℝ in l, ∀ (m : ℕ) (xs : Fin m → Site d), Function.Injective xs →
      ∀ lev : Fin m → ℝ,
        |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ i : Fin m, J σ (xs i) ≤ lev i}
          - ∏ i : Fin m, (centeredMassLaw d ν).real
            {σ : Site d → ℝ | J σ 0 ≤ lev i}| ≤ theta := by
    intro theta htheta K _
    exact Filter.Eventually.of_forall fun _R m xs hxs lev => by
      rw [indep_path_factorization ν J hJ m xs hxs lev, sub_self, abs_zero]
      exact htheta.le
  have hunif := fun ε hε c hc => eventually_uniform_survival_core hd ν hvar' J hshift hnull
    T hT κ hκ hthresholds' (fun theta htheta K hK =>
      (hfact theta htheta K hK).mono fun R hR m xs hxs _ lev _ _ => hR m xs hxs lev) ε hε c hc hl
  refine ⟨(tendsto_averaged_survival_of_uniform ν T κ hT hκ hunif hl).comp hscale,
    4 * (κ * green d 0 0), ?_⟩
  intro δ hδ
  obtain ⟨efun, he0, hetop, hebound⟩ := exists_cov_bound_core hd ν hvar' J
    hshift hnull T hT κ hκ hthresholds' (fun theta htheta K hK =>
      (hfact theta htheta K hK).mono fun R hR m xs hxs _ lev _ _ => hR m xs hxs lev) δ hδ hl
  exact ⟨fun k => efun (Rseq k), fun k => he0 (Rseq k), hetop.comp hscale,
    fun k i j hi hj X Y _ _ => hebound (Rseq k) i j hi hj X Y⟩

end Sandpile.Support
