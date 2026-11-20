import Sandpile.Support.D4MembraneCoefficientL2
import Sandpile.Support.SquareSummableMassCLT

/-!
# Scalar convergence reduced to potential-kernel coefficients

The paired defect transfers the weighted central limit theorem from the
potential-kernel coefficients to the finite-time membrane pairing. It remains
to establish uniform smallness and the limiting `ℓ²` norm of those potential
coefficients by Fourier analysis.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped lp ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The square-summable vector of potential-kernel coefficients of a cell
pairing. -/
noncomputable def potentialCellVector (hHK : Sandpile.External.HeatKernelBounds)
    (R : ℝ) (ψ : Space 4 → ℝ) (s : Finset (Site 4)) : ℓ²(Site 4, ℝ) :=
  ⟨cellKernelCoeff R ψ s (potentialKernel 4), memℓp_potential_cellKernelCoeff hHK R ψ s⟩

/-- The square-summable vector of finite-time Green coefficients of a cell
pairing. -/
noncomputable def greenTimeCellVector (R : ℝ) (t : ℕ) (ψ : Space 4 → ℝ)
    (s : Finset (Site 4)) : ℓ²(Site 4, ℝ) :=
  ⟨cellKernelCoeff R ψ s (greenTime 4 t), memℓp_greenTime_cellKernelCoeff R t ψ s⟩

/-- Scalar membrane convergence follows from the potential coefficients'
smallness and limiting norm together with the paired squared-defect hypothesis. -/
theorem tendstoInDistribution_omegaRep_membrane_of_potential_coefficients
    (hHK : Sandpile.External.HeatKernelBounds)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (D : Set (Space 4)) (w φ : Space 4 → ℝ) (T : ℝ → ℕ)
    (s : ℝ → Finset (Site 4)) (hint : Integrable (omegaShift D w φ))
    (hs : ∀ R z, omegaShift D w φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s R)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, ∀ y,
      |potentialCellVector hHK R (omegaShift D w φ) (s R) y| ≤ δ)
    (B : ℝ) (hB : Tendsto
      (fun R => ‖potentialCellVector hHK R (omegaShift D w φ) (s R)‖) atTop (𝓝 B))
    (hdefect : Tendsto (fun R : ℝ => ∑' y : Site 4,
      ENNReal.ofReal (Sandpile.External.membraneDefect R (T R) D w φ y ^ 2))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site 4 → ℝ) =>
        omegaRep D w (latticePairing R (membrane (scenery 4 σ) (T R))) φ)
      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * B ^ 2))) := by
  classical
  let S : ℝ → Finset (Site 4) := fun R => (s R).biUnion (fun x => boxFinset x (T R))
  have hS : ∀ R x, x ∈ s R → boxFinset x (T R) ⊆ S R := by
    intro R x hx y hy
    exact Finset.mem_biUnion.mpr ⟨x, hx, hy⟩
  let a : ℝ → ℓ²(Site 4, ℝ) :=
    fun R => greenTimeCellVector R (T R) (omegaShift D w φ) (s R)
  let b : ℝ → ℓ²(Site 4, ℝ) :=
    fun R => potentialCellVector hHK R (omegaShift D w φ) (s R)
  have ha : ∀ R y, y ∉ S R → a R y = 0 := by
    intro R y hy
    exact cellKernelCoeff_greenTime_eq_zero (hS R) hy
  have hab : Tendsto (fun R => ∑' y, ENNReal.ofReal ((a R y - b R y) ^ 2))
      atTop (𝓝 0) := by
    convert hdefect using 1
    funext R
    apply tsum_congr
    intro y
    rw [membraneDefect_eq_coeff_sub R (T R) (s R) hint (hs R) y]
    rfl
  have hclt := tendstoInDistribution_linear_of_sq_defect_mass (d := 4) (by norm_num)
    ν hsq hmean a b S ha hsmall B hB hab
  refine TendstoInDistribution.congr (fun R => ?_) (Filter.Eventually.of_forall fun _ => rfl) hclt
  exact Filter.Eventually.of_forall fun σ =>
    (omegaRep_membrane_eq_sum R (T R) (scenery 4 σ) (s R) (S R)
      hint (hs R) (hS R)).symm

end Sandpile.Support
