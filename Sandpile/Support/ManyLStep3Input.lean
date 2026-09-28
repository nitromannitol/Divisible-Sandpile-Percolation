import Sandpile.Support.ManyLManyLimits
import Sandpile.Support.ContLogisticLaw

/-! # Naming Step 3's subsequential-convergence input

The Step-3 input of `thm:dgt4-many-limits` (`sandpile.tex:5900-5928`), named.

`ManyLStep3Input d ν` is the subsequential convergence of the rescaled centred
odometer along a single sequence of scales, exactly the `hsub` argument of
`dgt4_many_limits_of_sub`.  `dgt4_many_limits_of_step3` is the whole node with
the scenery law discharged from `exists_scenery_law`, so the frozen theorem
follows by one application the moment `ManyLStep3Input` is available at that
law.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

section

variable {d : ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- The Step-3 input of `thm:dgt4-many-limits`: the subsequential convergence of
the rescaled centred odometer along a single sequence of scales.  This is the
`hsub` argument of `dgt4_many_limits_of_sub`, named so that the frozen node's
proof is a one-line discharge. -/
def ManyLStep3Input : Prop :=
  ∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
    ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
      ∃ kl : ℕ → ℕ, StrictMono kl ∧
        ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
          Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
            (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
              Rseq (kl ⌊L⌋₊) ^ (((d : ℝ) - 4) / 2) *
                Sandpile.Continuum.latticePairing (Rseq (kl ⌊L⌋₊))
                  (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                      ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊) φ)
            (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)

end

/-- **`thm:dgt4-many-limits` from the Step-3 input.**  The scenery law and its
four analytic clauses come from `exists_scenery_law`; the Step-3 input is the
hypothesis, at that law. -/
theorem dgt4_many_limits_of_step3 (d : ℕ) (hd : 5 ≤ d)
    (hstep3 : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      (∫ z, z ∂ν = 0) → variance (id : ℝ → ℝ) ν = 1 →
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) →
      (∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
        Integrable (fun z => Real.exp (θ * |z|)) ν ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
            -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r) →
      ManyLStep3Input (d := d) (ν := ν)) :
    ∃ ν : Measure ℝ, ∃ _ : IsProbabilityMeasure ν,
      ∫ z, z ∂ν = 0 ∧ variance (id : ℝ → ℝ) ν = 1 ∧
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) ∧
      (∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
        Integrable (fun z => Real.exp (θ * |z|)) ν ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
            -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r) ∧
      (∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
        ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
          ∃ kl : ℕ → ℕ, StrictMono kl ∧
            ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
              Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
                (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
                  Rseq (kl ⌊L⌋₊) ^ (((d : ℝ) - 4) / 2) *
                    Sandpile.Continuum.latticePairing (Rseq (kl ⌊L⌋₊))
                      (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊ x -
                        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                          ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊) φ)
                (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)) ∧
      ∀ T : ℝ, 0 < T → ∀ κ κ' : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
        κ' ∈ Set.Icc ((3 : ℝ) / 2) 2 → κ ≠ κ' →
        ∃ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ ∧
          Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ ≠
            Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ' T φ φ := by
  obtain ⟨ν, hprob, hmean, hvar, hdens, htail⟩ := exists_scenery_law
  exact dgt4_many_limits_of_sub d hd ν hprob hmean hvar hdens htail
    (hstep3 ν hmean hvar hdens htail)


end Sandpile.Support
