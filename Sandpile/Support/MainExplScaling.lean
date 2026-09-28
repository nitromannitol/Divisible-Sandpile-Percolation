import Sandpile.Support.MainExplInterpolationNorm

/-!
# Finite-dimensional limit and tightness of the interpolated odometer

The finite-dimensional limit and compact tightness estimates for the multilinearly
interpolated, rescaled odometer, using the local central limit input and stability of
continuum stopping values, are assembled into the single statement
`Sandpile.brownian_scaling_limit_of_localCLT`: convergence in distribution of every finite
family of point evaluations (from `Sandpile.brownian_scaling_fdd_of_localCLT`), a uniform
norm bound on every compact set (from `Sandpile.exists_interpolation_norm_bound`), and a
uniform modulus-of-continuity bound on every compact set (from
`Sandpile.exists_interpolation_modulus`).
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

universe u

/-- The interpolated scaling limit, with the local central limit input explicit. -/
theorem Sandpile.brownian_scaling_limit_of_localCLT
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[P] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω' → Sandpile.Continuum.Space d)
    (hB : ∀ x : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d x (B x) P')
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : Ω'), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T) :
    (∀ (m : ℕ) (x : Fin m → Sandpile.Continuum.Space d),
        TendstoInDistribution
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (j : Fin m) =>
            Sandpile.Continuum.multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) (x j))
          atTop
          (fun (ω : Ω) (j : Fin m) =>
            Sandpile.Continuum.brownianValue (B (x j)) P'
              (fun t y => Z t y ω)
              T (x j))
          (fun _ => Sandpile.centeredMassLaw d ν) P) ∧
      ∀ K : Set (Sandpile.Continuum.Space d), IsCompact K →
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
          Sandpile.centeredMassLaw d ν
              {σ | ∃ z ∈ K, M < |Sandpile.Continuum.multilinearInterp R
                (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z|} ≤
            ENNReal.ofReal ε) ∧
        (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
          Sandpile.centeredMassLaw d ν
              {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < δ ∧
                η < |Sandpile.Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z -
                  Sandpile.Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z'|} ≤
            ENNReal.ofReal ε)
 := by
  constructor
  · exact Sandpile.brownian_scaling_fdd_of_localCLT hLocalCLT hStab d hd hd3 ν
      hmean hvar hvar' θ₀ hθ₀ hexp Ω P W hW Z hZmod hZcont hZgrow Ω' P' B hB hBc hBm T hT
  · intro K hK
    constructor
    · intro ε hε
      obtain ⟨M, _, hM⟩ := Sandpile.exists_interpolation_norm_bound hLocalCLT hStab d hd hd3 ν
        hmean hvar hvar' θ₀ hθ₀ hexp Ω P W hW Z hZmod hZcont hZgrow Ω' P' B hB hBc hBm T hT K hK
        ε hε
      exact ⟨M, hM⟩
    · intro ε η hε hη
      exact Sandpile.exists_interpolation_modulus hLocalCLT d hd hd3 ν
        hmean hvar hvar' θ₀ hθ₀ hexp T hT K hK ε η hε hη
