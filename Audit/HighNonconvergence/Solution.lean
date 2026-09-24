import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: HighNonconvergence

The challenge module `Audit/HighNonconvergence/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.high_nonconvergence` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(iii)(d) (`thm:main-explosion`). -/
theorem high_nonconvergence
    (hInter : External.IntersectionSecondMoment)
    (hLocalCLT : External.LocalCLT)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : External.ContinuumBesovTightness (Site d → ℝ)) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ [_i : IsProbabilityMeasure ν],
      (∫ z, z ∂ν = 0) ∧ variance id ν = 1 ∧
      (∃ p : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ z : ℝ, 0 < p z) ∧
        ν = volume.withDensity fun z => ENNReal.ofReal (p z)) ∧
      (∃ θ₀ : ℝ, 0 < θ₀ ∧ Integrable (fun z => Real.exp (θ₀ * |z|)) ν) ∧
      ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
        Continuum.TightInNegSobolev d s (centeredMassLaw d ν)
            (Continuum.diffusiveFluctuation (centeredMassLaw d ν) T) ∧
          (∃ (I : Set ℝ) (K : ℝ → (Continuum.Space d → ℝ) →
              (Continuum.Space d → ℝ) → ℝ),
            ¬ I.Countable ∧
              (∀ κ ∈ I, ∀ κ' ∈ I, κ ≠ κ' →
                ∃ φ : Continuum.Space d → ℝ,
                  Continuum.IsTestFn Set.univ φ ∧
                    gaussianReal 0 (Real.toNNReal (K κ φ φ)) ≠
                      gaussianReal 0 (Real.toNNReal (K κ' φ φ))) ∧
              ∀ κ ∈ I, ∃ Rs : ℕ → ℝ, Tendsto Rs atTop atTop ∧
                ∀ φ : Continuum.Space d → ℝ,
                  Continuum.IsTestFn Set.univ φ →
                    TendstoInDistribution
                      (fun (k : ℕ) (σ : Site d → ℝ) =>
                        Continuum.diffusiveFluctuation
                          (centeredMassLaw d ν) T (Rs k) σ φ)
                      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw d ν)
                      (gaussianReal 0 (Real.toNNReal (K κ φ φ)))) ∧
          ¬ ∃ K : (Continuum.Space d → ℝ) →
              (Continuum.Space d → ℝ) → ℝ,
            Continuum.TendstoInNegSobolev d s (centeredMassLaw d ν)
              (Continuum.diffusiveFluctuation (centeredMassLaw d ν) T) K := by
  rw [Bridge.diffusiveFluctuation_eq]
  exact Sandpile.high_nonconvergence (Bridge.intersectionSecondMoment hInter)
    (Bridge.localCLT hLocalCLT) d hd (Bridge.continuumBesovTightness _ hBesov)

end SandpileAudit
