import Sandpile.Support.ContManyLimits

/-! # Assembling the many-limits theorem

The assembly of `thm:dgt4-many-limits` (`sandpile.tex:5900-5928`).

The paper's proof (`sandpile.tex:5930-...`) has three steps.  Step 1 constructs
the scenery law and its tail profile; Step 2 proves the estimates for
`P(u_n(0)=0)` and the comparison with the threshold event; Step 3 applies
`lem:dgt4-path-survival` and `lem:dgt4-linearization-from-survival` along the
subsequence `R_{k_ℓ}` to obtain the field limits.

`Sandpile.Support.exists_scenery_law` (`Support/ContLogisticLaw.lean`) supplies
the four analytic clauses of the scenery, and
`Sandpile.Support.exists_testFn_weightedMembraneCov_ne`
(`Support/ContCovKappa.lean`) supplies the pairwise distinctness of the limit
laws.  `Sandpile.Support.dgt4_many_limits_of` (`Support/ContManyLimits.lean`)
assembles the node from those two and the Step-3 subsequential convergence,
which it carries as an explicit hypothesis.

The theorem below is the whole node with the scenery existentially quantified:
it discharges the scenery from `exists_scenery_law`, so the node follows by this
one application the moment the Step-3 subsequential convergence is available.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- **`thm:dgt4-many-limits` from the subsequential convergence.**  The scenery
law and its four analytic properties are produced by `exists_scenery_law`; the
convergence along the subsequences is the hypothesis, at that law; the
distinctness of the limit laws is proved in `dgt4_many_limits_of` from the
strict monotonicity of the covariance in the exponent. -/
theorem dgt4_many_limits_of_sub (d : ℕ) (hd : 5 ≤ d)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : variance (id : ℝ → ℝ) ν = 1)
    (hdens : ∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z))
    (htail : ∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
      Integrable (fun z => Real.exp (θ * |z|)) ν ∧
      ∀ᶠ r : ℝ in atTop,
        c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
          -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r)
    (hsub : ∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
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
              (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)) :
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
  exact dgt4_many_limits_of d (le_trans (by norm_num) hd) ν hprob hmean hvar hdens htail hsub

end Sandpile.Support
