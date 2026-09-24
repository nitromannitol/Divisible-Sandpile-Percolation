/-
Bounded optional sampling for continuous martingales.

The upper dyadic stopped values are conditional expectations of one integrable
terminal value. Their uniform integrability and pathwise convergence imply
integrability and preservation of expectation at every bounded stopping time.
-/
import Sandpile.Support.ExplOptionalSampling
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace Sandpile.Support

theorem integrable_stopped_martingale_eq_of_continuous {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝔽 P)
    (hMc : ∀ ω, Continuous fun t => M t ω)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝔽 fun ω => (τ ω : ℝ≥0∞))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => M (τ ω) ω) P ∧
      (∫ ω, M (τ ω) ω ∂P) = ∫ ω, M 0 ω ∂P := by
  let σ (n : ℕ) (ω : Ω) := LatticeProb.dyUp n (τ ω)
  have hσst (n : ℕ) : IsStoppingTime 𝔽 fun ω => (σ n ω : ℝ≥0∞) :=
    LatticeProb.isStoppingTime_dyUp hτ n
  have hσb (n : ℕ) (ω : Ω) : σ n ω ≤ T + 1 := by
    have hi : ((2 : ℝ≥0) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
    exact (LatticeProb.dyUp_le_add n (τ ω)).trans (add_le_add (hbound ω) hi)
  have he (n : ℕ) : (fun ω => M (σ n ω) ω) =ᵐ[P]
      P[M (T + 1) | (hσst n).measurableSpace] := by
    have hh := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hσst n)
      (fun ω => ENNReal.coe_le_coe.mpr (hσb n ω)) (LatticeProb.countable_range_dyUp n τ)
    filter_upwards [hh] with ω hω
    exact hω
  have hUI : UniformIntegrable (fun n ω => M (σ n ω) ω) 1 P :=
    ((hM.integrable (T + 1)).uniformIntegrable_condExp
      (fun n => (hσst n).measurableSpace_le)).ae_eq (fun n => (he n).symm)
  have ht : ∀ᵐ ω ∂P, Tendsto (fun n => M (σ n ω) ω) atTop (𝓝 (M (τ ω) ω)) :=
    Eventually.of_forall fun ω => (hMc ω).tendsto (τ ω) |>.comp (LatticeProb.tendsto_dyUp (τ ω))
  have hI : Integrable (fun ω => M (τ ω) ω) P := hUI.integrable_of_ae_tendsto ht
  have hLp := tendsto_Lp_finite_of_tendsto_ae (p := (1 : ℝ≥0∞)) le_rfl ENNReal.one_ne_top
    hUI.1 (memLp_one_iff_integrable.mpr hI) hUI.2.1 ht
  have hlim := tendsto_integral_of_L1' _ hI.aestronglyMeasurable
    (Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hUI.memLp n)) hLp
  have hσI (n : ℕ) : (∫ ω, M (σ n ω) ω ∂P) = ∫ ω, M (T + 1) ω ∂P := by
    rw [integral_congr_ae (he n), integral_condExp (hσst n).measurableSpace_le]
  have hlast : (∫ ω, M (τ ω) ω ∂P) = ∫ ω, M (T + 1) ω ∂P :=
    tendsto_nhds_unique hlim (by simpa only [hσI] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ ω, M (T + 1) ω ∂P) atTop
        (𝓝 (∫ ω, M (T + 1) ω ∂P))))
  have hzero : (∫ ω, M 0 ω ∂P) = ∫ ω, M (T + 1) ω ∂P := by
    simpa using hM.setIntegral_eq (show (0 : ℝ≥0) ≤ T + 1 from zero_le) MeasurableSet.univ
  exact ⟨hI, hlast.trans hzero.symm⟩


end Sandpile.Support
