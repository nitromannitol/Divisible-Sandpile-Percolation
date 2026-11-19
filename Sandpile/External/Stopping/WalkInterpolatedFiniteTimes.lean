import Sandpile.External.Stopping.WalkGridFiniteTimes
import Sandpile.External.Stopping.WalkFloorInterpolation

/-!
# Finite-dimensional limits of interpolated walks

The interpolation error vanishes uniformly at the observation times, so the
finite-dimensional grid limits also hold for the continuous interpolations.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Diffusively rescaled interpolated walks converge at any finite family of times. -/
theorem tendstoInDistribution_walk_interpolated_finite_times
    {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (u : ι → ℝ≥0)
    (x : ℕ → Site d) (y : Continuum.Space d)
    (hx : Tendsto (fun n => Lclt.scaledSite (R n) (x n)) atTop (𝓝 y))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    TendstoInDistribution
      (fun n (X : ℕ → Site d) (p : ι × Fin d) => diffusiveWalk (R n) (u p.1) X p.2)
      atTop (fun ω (p : ι × Fin d) => y p.2 + B (u p.1) ω p.2)
      (fun n => LatticeProb.siteWalkLaw d (x n)) P := by
  let Q := LatticeProb.incPathLaw d
  let S : ℕ → (ℕ → Site d) → (ℕ → Site d) := fun n => LatticeProb.sitePath (x n)
  let Z : ℕ → (ℕ → Site d) → (ι × Fin d → ℝ) := fun n X p =>
    Lclt.scaledSite (R n) (X ⌊(u p.1 : ℝ) * (R n) ^ 2⌋₊) p.2
  let Y : ℕ → (ℕ → Site d) → (ι × Fin d → ℝ) := fun n X p =>
    diffusiveWalk (R n) (u p.1) X p.2
  have hZ (n : ℕ) : Measurable (Z n) := by
    apply Measurable.of_eval
    intro p
    exact (measurable_of_countable (fun z : Site d => Lclt.scaledSite (R n) z p.2)).comp
      (measurable_pi_apply _)
  have hY (n : ℕ) : Measurable (Y n) := by
    apply Measurable.of_eval
    intro p
    exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) p.2).measurable.comp
      (measurable_linearWalk (R n) _)
  have hS (n : ℕ) : Measurable (S n) := LatticeProb.measurable_sitePath (x n)
  have hgrid := tendstoInDistribution_walk_grid_finite_times R hR u x y hx P B hB
  have hgrid' : TendstoInDistribution (fun n => Z n ∘ S n) atTop
      (fun ω (p : ι × Fin d) => y p.2 + B (u p.1) ω p.2) (fun _ => Q) P := by
    refine ⟨fun n => ((hZ n).comp (hS n)).aemeasurable, hgrid.aemeasurable_limit, ?_⟩
    have heq : (fun n => (⟨Q.map (Z n ∘ S n), inferInstance⟩ :
        ProbabilityMeasure (ι × Fin d → ℝ))) =
        (fun n => ⟨(LatticeProb.siteWalkLaw d (x n)).map (Z n), inferInstance⟩) := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      change Q.map (Z n ∘ S n) = (LatticeProb.siteWalkLaw d (x n)).map (Z n)
      rw [LatticeProb.siteWalkLaw_eq, Measure.map_map (hZ n) (hS n)]
    rw [heq]
    exact hgrid.tendsto
  have hpos : ∀ᶠ n in atTop, 0 < R n := hR.eventually (eventually_gt_atTop 0)
  have hae (n : ℕ) (hn : 0 < R n) : ∀ᵐ ξ ∂Q, ∀ s : ℝ≥0,
      ‖linearWalk (R n) s (S n ξ) - Lclt.scaledSite (R n) ((S n ξ) ⌊(s : ℝ)⌋₊)‖ ≤ 1 / R n := by
    have h := ae_norm_linearWalk_sub_floor_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) (x n) (R n) hn
    change ∀ᵐ X ∂(Q.map (S n)), _ at h
    exact ae_of_ae_map (hS n).aemeasurable h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
  have hall : ∀ᵐ ξ ∂Q, ∀ n, N ≤ n → ∀ s : ℝ≥0,
      ‖linearWalk (R n) s (S n ξ) - Lclt.scaledSite (R n) ((S n ξ) ⌊(s : ℝ)⌋₊)‖ ≤ 1 / R n := by
    apply ae_all_iff.mpr
    intro n
    by_cases hn : N ≤ n
    · filter_upwards [hae n (hN n hn)] with ξ hξ
      exact fun _ => hξ
    · exact Filter.Eventually.of_forall (fun _ h => (hn h).elim)
  have herr : ∀ᵐ ξ ∂Q, Tendsto (fun n => (Y n (S n ξ) - Z n (S n ξ))) atTop (𝓝 0) := by
    filter_upwards [hall] with ξ hξ
    apply tendsto_pi_nhds.mpr
    intro p
    apply squeeze_zero_norm'
    · filter_upwards [eventually_ge_atTop N] with n hn
      have h := hξ n hn (⟨(R n)^2, sq_nonneg _⟩ * u p.1)
      have hcoord := PiLp.norm_apply_le (linearWalk (R n) (⟨(R n)^2, sq_nonneg _⟩ * u p.1) (S n ξ) -
      Lclt.scaledSite (R n) ((S n ξ) ⌊(((⟨(R n)^2, sq_nonneg _⟩ : ℝ≥0) * u p.1) : ℝ)⌋₊)) p.2
      simpa [Y, Z, diffusiveWalk, mul_comm, one_div] using hcoord.trans h
    · exact tendsto_inv_atTop_zero.comp hR
  have hmeasure := tendstoInMeasure_of_tendsto_ae
    (fun n => (((hY n).comp (hS n)).sub ((hZ n).comp (hS n))).aestronglyMeasurable) herr
  have hlim := tendstoInDistribution_of_tendstoInMeasure_sub (fun n => Y n ∘ S n)
    (fun ω (p : ι × Fin d) => y p.2 + B (u p.1) ω p.2) hgrid' hmeasure
    (fun n => ((hY n).comp (hS n)).aemeasurable)
  refine ⟨fun n => (hY n).aemeasurable, hlim.aemeasurable_limit, ?_⟩
  have heq : (fun n => (⟨(LatticeProb.siteWalkLaw d (x n)).map (Y n), inferInstance⟩ :
      ProbabilityMeasure (ι × Fin d → ℝ))) =
      (fun n => ⟨Q.map (Y n ∘ S n), inferInstance⟩) := by
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    change (LatticeProb.siteWalkLaw d (x n)).map (Y n) = Q.map (Y n ∘ S n)
    rw [LatticeProb.siteWalkLaw_eq, Measure.map_map (hY n) (hS n)]
  rw [heq]
  exact hlim.tendsto

end Sandpile.External.Stopping
