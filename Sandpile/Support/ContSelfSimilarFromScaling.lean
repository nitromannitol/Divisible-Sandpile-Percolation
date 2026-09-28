import Sandpile.Support.ContSelfSimilarLimit
import Sandpile.Support.ContSelfSimilarMesh
import Sandpile.Support.ContSelfSimilarMoments
import Sandpile.Support.ContClause1
import Sandpile.Support.MeanAMean
import Sandpile.Support.MeanAExpLimit
import Sandpile.Support.MeanALimit
import Sandpile.Support.Dgt4OriginProb

/-!
# Self-similarity from the parabolic scaling limit

The three clauses of the continuum-value proposition, derived from the parabolic scaling
limit hypothesis `hScaling` on the rescaled odometer. Given the finite-dimensional
convergence of `rescaledOdometer` to `continuumValue d Z B PB` together with the tightness
and equicontinuity bounds that `hScaling` packages,
`continuum_value_self_similar_of_parabolic_limit` derives: a measurable version of the
continuum value that is self-similar in law, with `continuumValue T x` having the law of
`T^{(4-d)/4} • continuumValue 1 0` (`clause1_of_transfers`); a uniform exponential moment
for the rescaled odometer (`exists_uniform_exp_moment_rescaled_mass`) that transfers to
integrability of `exp(θ · continuumValue 1 0)` (`integrable_exp_of_uniform_exp`); and
positive `p`-th power moments of `continuumValue T x` for every `p > 0`, related to the
moment at `(1,0)` by the same self-similar scaling exponent
(`continuumValue_power_moments`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support
open Sandpile.Continuum

/-- Self-similarity, uniform exponential integrability and positive power moments.
The explicit input is the conclusion of the parabolic scaling theorem, for this
field and motion at every positive horizon. -/
theorem continuum_value_self_similar_of_parabolic_limit
    {ΩW ΩB : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (PB : Measure ΩB) (B : Space d → ℝ≥0 → ΩB → Space d)
    (hScaling : ∀ T : ℝ, 0 < T →
    (∀ (m : ℕ) (x : Fin m → Sandpile.Continuum.Space d),
        TendstoInDistribution
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (j : Fin m) =>
            Sandpile.Continuum.multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) (x j))
          atTop
          (fun (ω : ΩW) (j : Fin m) =>
            Sandpile.Continuum.brownianValue (B (x j)) PB
              (fun t y => Z t y ω)
              T (x j))
          (fun _ => Sandpile.centeredMassLaw d ν) PW) ∧
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
            ENNReal.ofReal ε)) :
    (∃ U : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ,
      (∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d,
        Measurable (U T x) ∧
        U T x =ᵐ[PW] fun ω =>
          Sandpile.Continuum.continuumValue d Z B PB T x ω) ∧
      ∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d,
        PW.map (U T x) = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧
      (∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
        Integrable (fun σ => Real.exp (θ *
          Sandpile.Continuum.rescaledOdometer d R 1 0 σ))
          (Sandpile.centeredMassLaw d ν) ∧
        ∫ σ, Real.exp (θ *
          Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
          ∂(Sandpile.centeredMassLaw d ν) ≤ M) ∧
      Integrable (fun ω => Real.exp (θ *
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω)) PW) ∧
    (∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d, ∀ p : ℝ, 0 < p →
      Integrable (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB T x ω ^ p) PW ∧
      Integrable (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω ^ p) PW ∧
      ∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ^ p ∂PW =
        T ^ (p * (4 - (d : ℝ)) / 4) *
          ∫ ω, Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω ^ p ∂PW ∧
      0 < ∫ ω, Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω ^ p ∂PW) := by
  have hlimit : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      TendstoInDistribution (fun R : ℝ => rescaledOdometer d R T x)
        atTop (continuumValue d Z B PB T x) (fun _ => Sandpile.centeredMassLaw d ν) PW := by
    intro T hT x
    have hfd := ((hScaling T hT).1 1 (fun _ => x)).continuous_comp
      (g := fun v : Fin 1 → ℝ => v 0) (continuous_apply 0)
    exact tendstoInDistribution_rescaled_of_interp d ν PW _ T x hfd
      (fun K hK => ((hScaling T hT).2 K hK).2)
  have hmeas := fun T hT x => (hlimit T hT x).aemeasurable_limit
  have hlaw := selfsimilar_of_rescaled_limit d ν PW (continuumValue d Z B PB) hlimit
  have hres := tendstoInDistribution_comp (fun r : Set.Ici (1 : ℝ) => (r : ℝ))
    (tendsto_val_Ici_atTop 1) (hlimit 1 one_pos 0)
  have hnn : ∀ᵐ ω ∂PW, 0 ≤ continuumValue d Z B PB 1 0 ω :=
    ae_nonneg_of_tendstoInDistribution hres (fun r => ae_of_all _ fun σ =>
      rescaledOdometer_nonneg d (lt_of_lt_of_le zero_lt_one r.2) 1 0 σ)
  have hsq := integrable_sq_of_evariance ν hvar'
  obtain ⟨K, hK⟩ := exists_uniform_mean_rescaled_of_tightness d hd hd3 ν hsq
    (((hScaling 1 one_pos).2 {0} isCompact_singleton).1)
  obtain ⟨θ, A, hθ, hA⟩ := exists_uniform_exp_moment_rescaled_mass d hd hd3
    θ₀ (∫ z, Real.exp (θ₀ * |z|) ∂ν) hθ₀
  have hD := hA ν inferInstance hexp le_rfl K hK
  let C := Real.exp (θ * K) * A
  have hC : 0 ≤ C := (integral_nonneg fun σ =>
    Real.exp_nonneg (θ * rescaledOdometer d 1 1 0 σ)).trans (hD 1 le_rfl).2
  have hE := integrable_exp_of_uniform_exp hres hnn θ C hθ.le hC
    (Eventually.of_forall fun r => ⟨ae_of_all _ fun σ =>
      rescaledOdometer_nonneg d (lt_of_lt_of_le zero_lt_one r.2) 1 0 σ, hD r r.2⟩)
  refine ⟨clause1_of_transfers d (variance id ν) W PW hW Z hZmod hZcont B PB hmeas hlaw,
    ⟨θ, hθ, ⟨C, hD⟩, hE.1⟩, ?_⟩
  exact continuumValue_power_moments d hd hd3 PW PB W hW (variance id ν)
    (ENNReal.toReal_pos hvar.ne' hvar'.ne) Z hZmod hZcont B hmeas hnn hlaw θ hθ hE.1

end Sandpile.Support
