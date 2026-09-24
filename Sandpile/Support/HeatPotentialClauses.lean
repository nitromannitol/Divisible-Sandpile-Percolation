/-
The two clauses of `prop:dlt4-heat-potential-invariance` (`sandpile.tex:1841-1848`),
each from the corresponding input, and their conjunction.

The finite-dimensional clause is the continuum convergence of the rescaled
double-time sums (`Sandpile.Support.heat_potential_fd`), and the tightness
clause is the quantitative Kolmogorov criterion applied to the interpolated
field (`Sandpile.Support.heat_potential_tightness_of_criterion`), whose two
statements are the library's `LatticeProb.kolmogorovModulusPi` and
`LatticeProb.kolmogorovBoundPi`.
-/
import Sandpile.Support.ContKolmogorovAssembly
import Sandpile.Support.ContContinuumMCT
import Sandpile.Support.ExpMomentRpow
import Sandpile.External.HeatKernelBoundsProved

open MeasureTheory ProbabilityTheory Filter
open Sandpile.Frozen.HeatPotentialInvariance

namespace Sandpile.Support

variable {d : ℕ}

set_option linter.unusedVariables false in
/-- **The finite-dimensional clause of `prop:dlt4-heat-potential-invariance`.** -/
theorem heat_potential_invariance_clause1
    (hLocalCLT : Sandpile.External.LocalCLT)
    (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (T : ℝ) (hT : 0 < T) :
    ∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Sandpile.Continuum.Space d),
      (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
      TendstoInDistribution
        (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (i : Fin m) =>
          linInterp d R (Sandpile.scenery d σ) (r i) (w i))
        atTop
        (fun (ω : ΩW) (i : Fin m) =>
          Sandpile.Continuum.gaussianPotential d (variance id ν) W (r i) (w i) ω)
        (fun _ => Sandpile.centeredMassLaw d ν) PW := by
  have hsq : MemLp (id : ℝ → ℝ) 2 ν :=
    (ProbabilityTheory.evariance_lt_top_iff_memLp aestronglyMeasurable_id).mp hvar'
  intro m r w hr
  have hL : ∀ i : Fin m, ‖w i‖ ≤ ∑ j : Fin m, ‖w j‖ :=
    fun i => Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  exact heat_potential_fd hLocalCLT hd0 hd ν hsq hmean PW W hW r (fun i => (hr i).1) w _ hL

/-- **The tightness clause of `prop:dlt4-heat-potential-invariance`.** -/
theorem heat_potential_invariance_clause2
    (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) :
    ∀ K : Set (ℝ × Sandpile.Continuum.Space d), IsCompact K →
      K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) →
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
        (Sandpile.centeredMassLaw d ν)
            {σ | ∃ p ∈ K, M < |linInterp d R (Sandpile.scenery d σ) p.1 p.2|} ≤
          ENNReal.ofReal ε) ∧
      (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
        (Sandpile.centeredMassLaw d ν)
            {σ | ∃ p ∈ K, ∃ q ∈ K, dist p q < δ ∧
              η < |linInterp d R (Sandpile.scenery d σ) p.1 p.2 -
                linInterp d R (Sandpile.scenery d σ) q.1 q.2|} ≤
          ENNReal.ofReal ε) := by
  intro K hK hKT
  have hd1 : 1 ≤ d := by omega
  have hmomν : ∀ p : ℝ, 2 ≤ p → Integrable (fun z => |z| ^ p) ν :=
    fun p hp => integrable_abs_rpow_of_exp_moment ν θ₀ hθ₀ hexp p (by linarith)
  exact heat_potential_tightness_of_criterion Sandpile.External.heatKernelBounds hd1 hd
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 < 1)
    kolmogorovModulusPi_holds kolmogorovBoundPi_holds ν hmean hmomν T hT K hK hKT

/-- **`prop:dlt4-heat-potential-invariance` from its two clauses.** -/
theorem heat_potential_invariance_of_clauses
    (hLocalCLT : Sandpile.External.LocalCLT)
    (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (T : ℝ) (hT : 0 < T) :
    (∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Sandpile.Continuum.Space d),
        (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
        TendstoInDistribution
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (i : Fin m) =>
            linInterp d R (Sandpile.scenery d σ) (r i) (w i))
          atTop
          (fun (ω : ΩW) (i : Fin m) =>
            Sandpile.Continuum.gaussianPotential d (variance id ν) W (r i) (w i) ω)
          (fun _ => Sandpile.centeredMassLaw d ν) PW) ∧
      (∀ K : Set (ℝ × Sandpile.Continuum.Space d), IsCompact K →
        K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) →
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
          (Sandpile.centeredMassLaw d ν)
              {σ | ∃ p ∈ K, M < |linInterp d R (Sandpile.scenery d σ) p.1 p.2|} ≤
            ENNReal.ofReal ε) ∧
        (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
          (Sandpile.centeredMassLaw d ν)
              {σ | ∃ p ∈ K, ∃ q ∈ K, dist p q < δ ∧
                η < |linInterp d R (Sandpile.scenery d σ) p.1 p.2 -
                  linInterp d R (Sandpile.scenery d σ) q.1 q.2|} ≤
            ENNReal.ofReal ε)) := by
  exact ⟨heat_potential_invariance_clause1 hLocalCLT d hd0 hd ν hmean hvar hvar' PW W hW T hT,
    heat_potential_invariance_clause2 d hd0 hd ν hmean θ₀ hθ₀ hexp T hT⟩

end Sandpile.Support
