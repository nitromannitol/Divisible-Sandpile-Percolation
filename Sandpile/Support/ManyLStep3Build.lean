import Sandpile.Support.Dgt4ABandStep23
import Sandpile.Support.Dgt4ATestedLinearizationSequence
import Sandpile.Support.ManyLStep3Input
import Sandpile.Support.ManyLSubseq
import Sandpile.Frozen.WeightedMembraneLimit

/-! # Composing Step 3: contact thresholds to field limits

Step 3: from the contact thresholds to the field limits.

The repository has Step 3's two halves but never composes them, so nothing
produces `ManyLStep3Input`.  The halves are:

  `dgt4_tested_linearization_of_thresholds_sequence`  the odometer fluctuation is
      approximated in `L²`, tested against a test function, by the weighted
      membrane sum, along any scale sequence carrying uniform contact thresholds;
  `Sandpile.Frozen.weighted_membrane_limit`  the weighted membrane sum itself
      converges in negative Sobolev, with covariance
      `generalWeightedMembraneCov d (variance ν) T q`.

Composing them is a Slutsky step: a sequence that is `L²`-close to a convergent
one converges to the same limit.  The weight the many-limits construction uses is
`q t = (1 - t/T)^κ`, and at that weight the general covariance is the `κ`
covariance, which is what the frozen statement names.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- **The weight of the many-limits construction identifies the two covariances.**
At `q t = (1 - t/T)^κ` the general weighted membrane covariance is the `κ` one. -/
theorem generalWeightedMembraneCov_eq_weighted (d : ℕ) (v T κ : ℝ) :
    Sandpile.Frozen.WeightedMembraneLimit.generalWeightedMembraneCov d v T
        (fun t => (1 - t / T) ^ κ)
      = weightedMembraneCov d v κ T := by
  funext φ ψ
  rfl

/-- **Step 3's input, from the contact thresholds.**  This is the composition the
repository was missing. -/
theorem manyLStep3Input_of_thresholds (d : ℕ) (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (_hHeat : Sandpile.External.HeatKernelBounds)
    (_hLocalCLT : Sandpile.External.LocalCLT)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance (id : ℝ → ℝ) ν)
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (hthr : ∃ R : ℕ → ℝ, StrictMono R ∧ Tendsto R atTop atTop ∧
      ∀ κ : ℝ, κ ∈ Icc ((3 : ℝ) / 2) 2 →
        ∃ kl : ℕ → ℕ, StrictMono kl ∧
          ∀ T : ℝ, 0 < T → UniformContactThresholdsAlong d ν κ T (R ∘ kl)) :
    ManyLStep3Input (d := d) (ν := ν) := by
  classical
  obtain ⟨R, hRmono, hRtop, hκ⟩ := hthr
  have hd1 : 1 ≤ d := by omega
  have : NeZero d := ⟨by omega⟩
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp aestronglyMeasurable_id).mp hvar'
  have hsq : Integrable (fun z : ℝ => z ^ 2) ν := hLp.integrable_sq
  have hpos : Integrable (fun z : ℝ => max z 0) ν := Sandpile.integrable_posPart_of_sq ν hsq
  refine ⟨R, hRmono, hRtop, fun κ hκmem => ?_⟩
  have hκ0 : 0 < κ := by linarith [hκmem.1]
  obtain ⟨kl, hklmono, hthrκ⟩ := hκ κ hκmem
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 ≤ R (kl N) :=
    ((hRtop.comp hklmono.tendsto_atTop).eventually_ge_atTop 1).exists
  have hkl'mono : StrictMono (fun n : ℕ => kl (n + N)) :=
    fun a b hab => hklmono (Nat.add_lt_add_right hab N)
  refine ⟨fun n => kl (n + N), hkl'mono, fun T hT s hs => ?_⟩
  have hg1 : ∀ L : ℝ, 1 ≤ R (kl (⌊L⌋₊ + N)) := fun L =>
    le_trans hN (hRmono.monotone (hklmono.monotone (Nat.le_add_left N _)))
  have hgtop : Tendsto (fun L : ℝ => R (kl (⌊L⌋₊ + N))) atTop atTop :=
    (hRtop.comp hkl'mono.tendsto_atTop).comp tendsto_nat_floor_atTop
  have hthr' : UniformContactThresholdsAlong d ν κ T (R ∘ fun n => kl (n + N)) :=
    fun ε hε η hη => (tendsto_add_atTop_nat N).eventually (hthrκ T hT ε hε η hη)
  have hq : ContinuousOn (fun t : ℝ => (1 - t / T) ^ κ) (Set.Icc 0 T) :=
    ContinuousOn.rpow_const (by fun_prop) (fun _ _ => Or.inr hκ0.le)
  have hW := Sandpile.Frozen.weighted_membrane_limit d hd hBesov T hT
    (fun t => (1 - t / T) ^ κ) hq ν hmean hvar hvar' s hs
  rw [generalWeightedMembraneCov_eq_weighted d (variance (id : ℝ → ℝ) ν) T κ]
    at hW
  have hlin : ∀ φ : Space d → ℝ, IsTestFn Set.univ φ →
      Tendsto (fun L : ℝ =>
        ∫ σ, (R (kl (⌊L⌋₊ + N)) ^ (((d : ℝ) - 4) / 2) *
          latticePairing (R (kl (⌊L⌋₊ + N)))
            (fun x => odometer σ ⌊R (kl (⌊L⌋₊ + N)) ^ 2 * T⌋₊ x -
              meanOdometer (centeredMassLaw d ν) ⌊R (kl (⌊L⌋₊ + N)) ^ 2 * T⌋₊ -
              ∑ j ∈ Finset.range ⌊R (kl (⌊L⌋₊ + N)) ^ 2 * T⌋₊,
                (fun t : ℝ => (1 - t / T) ^ κ) ((j : ℝ) / R (kl (⌊L⌋₊ + N)) ^ 2) *
                  (avg^[j] (scenery d σ)) x) φ) ^ 2
          ∂(centeredMassLaw d ν)) atTop (𝓝 0) := by
    intro φ hφ
    have h := dgt4_tested_linearization_of_thresholds_sequence d hd hGreen hInter ν hmean hvar'
      (R ∘ fun n => kl (n + N)) (hRmono.comp hkl'mono) (hRtop.comp hkl'mono.tendsto_atTop)
      T hT κ hκ0 hthr' φ hφ
    simpa only [Function.comp_def, div_div] using h.comp tendsto_nat_floor_atTop
  have hWd : ∀ φ : Space d → ℝ, IsTestFn Set.univ φ →
      TendstoInDistribution
        (fun L : ℝ => fun σ : Site d → ℝ =>
          R (kl (⌊L⌋₊ + N)) ^ (((d : ℝ) - 4) / 2) *
            latticePairing (R (kl (⌊L⌋₊ + N)))
              (fun x => ∑ j ∈ Finset.range ⌊R (kl (⌊L⌋₊ + N)) ^ 2 * T⌋₊,
                (fun t : ℝ => (1 - t / T) ^ κ) ((j : ℝ) / R (kl (⌊L⌋₊ + N)) ^ 2) *
                  (avg^[j] (scenery d σ)) x) φ)
        atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw d ν)
        (gaussianReal 0 (Real.toNNReal
          (weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ))) := fun φ hφ =>
    tendstoInDistribution_comp_atTop_real (centeredMassLaw d ν) _ _
      (fun L : ℝ => R (kl (⌊L⌋₊ + N))) hgtop (hW.1 φ hφ)
  have key := dgt4_subsequential_convergence d hGreen hBesov hd ν hsq hpos κ T hT s hs
    (fun L : ℝ => R (kl (⌊L⌋₊ + N))) (fun t : ℝ => (1 - t / T) ^ κ) (fun L _ => hg1 L)
    hlin hWd
  simpa only [mul_comm T] using key

end Sandpile.Support
