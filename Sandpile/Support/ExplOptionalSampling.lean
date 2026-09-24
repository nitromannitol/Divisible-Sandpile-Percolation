/-
Bounded optional sampling for continuous martingales and an integrable form of
Brownian restart.

Countable stopping times follow from conditional expectation. Upper dyadic
approximations of a bounded stopping time converge along continuous sample paths;
a common integrable envelope permits dominated convergence of the expectations.
Stopping-time measurability is an explicit hypothesis.

The restart identity for an integrable functional follows from the product law
of the past and the restarted path, by the map formula and ordinary Fubini.
-/
import Mathlib
import LatticeProb.Prob.StoppingDyadic
import LatticeProb.Prob.BrownianRestartIntegral

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

theorem integral_stopped_martingale_eq_of_countable_range {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝔽 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝔽 P)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝔽 fun ω => (τ ω : ℝ≥0∞))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T)
    (hc : (Set.range fun ω => (τ ω : ℝ≥0∞)).Countable) :
    (∫ ω, M (τ ω) ω ∂P) = ∫ ω, M T ω ∂P := by
  have hb : ∀ ω, (τ ω : ℝ≥0∞) ≤ (T : ℝ≥0∞) :=
    fun ω => ENNReal.coe_le_coe.mpr (hbound ω)
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hb hc
  have he' : (fun ω => M (τ ω) ω) =ᵐ[P] P[M T | hτ.measurableSpace] := by
    filter_upwards [he] with ω hω
    change M (τ ω) ω = _ at hω
    exact hω
  rw [integral_congr_ae he', integral_condExp hτ.measurableSpace_le]

theorem integrable_stopped_martingale_and_integral_eq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝔽 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝔽 P)
    (hMc : ∀ ω, Continuous fun t => M t ω)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝔽 fun ω => (τ ω : ℝ≥0∞))
    (hτm : Measurable τ) (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T)
    (D : Ω → ℝ) (hD : Integrable D P)
    (hdom : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, r ≤ T + 1 → ‖M r ω‖ ≤ D ω) :
    Integrable (fun ω => M (τ ω) ω) P ∧
      (∫ ω, M (τ ω) ω ∂P) = ∫ ω, M 0 ω ∂P := by
  have hjoint : StronglyMeasurable (Function.uncurry M) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hMc
      (fun _ => hM.stronglyAdapted.stronglyMeasurable)
  have hτv : AEStronglyMeasurable (fun ω => M (τ ω) ω) P :=
    (hjoint.comp_measurable (hτm.prodMk measurable_id)).aestronglyMeasurable
  have hτint : Integrable (fun ω => M (τ ω) ω) P := by
    refine hD.mono' hτv ?_
    filter_upwards [hdom] with ω hω
    exact hω (τ ω) ((hbound ω).trans (le_add_of_nonneg_right zero_le))
  let σ (n : ℕ) (ω : Ω) := LatticeProb.dyUp n (τ ω)
  have hσst (n : ℕ) : IsStoppingTime 𝔽 fun ω => (σ n ω : ℝ≥0∞) :=
    LatticeProb.isStoppingTime_dyUp hτ n
  have hσm (n : ℕ) : Measurable (σ n) := LatticeProb.measurable_of_isStoppingTime (hσst n)
  have hσb (n : ℕ) (ω : Ω) : σ n ω ≤ T + 1 := by
    have hi : ((2 : ℝ≥0) ^ n)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
    exact (LatticeProb.dyUp_le_add n (τ ω)).trans (add_le_add (hbound ω) hi)
  have hσI (n : ℕ) : (∫ ω, M (σ n ω) ω ∂P) = ∫ ω, M (T + 1) ω ∂P :=
    integral_stopped_martingale_eq_of_countable_range P 𝔽 M hM (σ n) (hσst n) (T + 1) (hσb n)
      (LatticeProb.countable_range_dyUp n τ)
  have hlim : Tendsto (fun n => ∫ ω, M (σ n ω) ω ∂P) atTop
      (𝓝 (∫ ω, M (τ ω) ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence D
      (fun n => (hjoint.comp_measurable ((hσm n).prodMk measurable_id)).aestronglyMeasurable)
      hD (fun n => hdom.mono fun ω hω => hω (σ n ω) (hσb n ω)) ?_
    exact Eventually.of_forall fun ω => (hMc ω).tendsto (τ ω) |>.comp (LatticeProb.tendsto_dyUp (τ ω))
  have he : (∫ ω, M (τ ω) ω ∂P) = ∫ ω, M (T + 1) ω ∂P := by
    apply tendsto_nhds_unique hlim
    simpa only [hσI] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ ω, M (T + 1) ω ∂P)
      atTop (𝓝 (∫ ω, M (T + 1) ω ∂P)))
  have hzero : (∫ ω, M 0 ω ∂P) = ∫ ω, M (T + 1) ω ∂P := by
    simpa using hM.setIntegral_eq (show (0 : ℝ≥0) ≤ T + 1 from zero_le) MeasurableSet.univ
  exact ⟨hτint, he.trans hzero.symm⟩


open LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem setIntegral_restart_of_integrable [IsProbabilityMeasure P] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (h : HasStrongMarkovRestart B P 𝔽)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝔽 fun ω => (τ ω : ℝ≥0∞))
    (hmshift : Measurable fun ω (t : ℝ≥0) => B (τ ω + t) ω - B (τ ω) ω)
    (hmshift0 : Measurable fun ω (t : ℝ≥0) => B t ω - B 0 ω)
    {α : Type*} [MeasurableSpace α] {Y : Ω → α} (hY : Measurable[hτ.measurableSpace] Y)
    {E : Set Ω} (hE : MeasurableSet[hτ.measurableSpace] E)
    {F : α × (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ} (hF : Measurable F)
    (hint : Integrable F
      ((Measure.map Y (P.restrict E)).prod
        (Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P))) :
    ∫ ω in E, F (Y ω, fun t => B (τ ω + t) ω - B (τ ω) ω) ∂P
      = ∫ ω in E, (∫ z, F (Y ω, z) ∂(P.map fun ω (t : ℝ≥0) => B t ω - B 0 ω)) ∂P := by
  have hYm : Measurable Y := hY.mono hτ.measurableSpace_le le_rfl
  have hW : Measurable fun ω => (Y ω, fun t : ℝ≥0 => B (τ ω + t) ω - B (τ ω) ω) :=
    hYm.prodMk hmshift
  haveI : IsFiniteMeasure (Measure.map Y (P.restrict E)) :=
    ⟨by rw [Measure.map_apply hYm MeasurableSet.univ, Set.preimage_univ]
        exact measure_lt_top _ _⟩
  haveI : IsProbabilityMeasure (Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P) :=
    Measure.isProbabilityMeasure_map hmshift0.aemeasurable
  have hG : StronglyMeasurable fun y : α =>
      ∫ z, F (y, z) ∂(Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P) :=
    hF.stronglyMeasurable.integral_prod_right'
  calc ∫ ω in E, F (Y ω, fun t => B (τ ω + t) ω - B (τ ω) ω) ∂P
      = ∫ p, F p ∂(Measure.map
          (fun ω => (Y ω, fun t : ℝ≥0 => B (τ ω + t) ω - B (τ ω) ω)) (P.restrict E)) :=
        (integral_map hW.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂((Measure.map Y (P.restrict E)).prod
          (Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P)) := by
        rw [h.map_prod hτ hmshift hmshift0 hY hE]
    _ = ∫ y, (∫ z, F (y, z) ∂(Measure.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P))
          ∂(Measure.map Y (P.restrict E)) := integral_prod _ hint
    _ = ∫ ω in E, (∫ z, F (Y ω, z) ∂(Measure.map
          (fun ω (t : ℝ≥0) => B t ω - B 0 ω) P)) ∂P :=
        integral_map hYm.aemeasurable hG.aestronglyMeasurable

end Sandpile.Support
