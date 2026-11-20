import Sandpile.External.Stopping.WalkGridLowerLimit
import Sandpile.External.Stopping.CenteredWalkCoupling
import Sandpile.External.Stopping.BrownianValueIntrinsic

/-!
# Brownian lower bound for lattice stopping values

The centered walk coupling and invariance principle identify the continuous
limit in the lower lattice bound with Brownian motion.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Along convergent starts and diverging scales, the Brownian stopping value
is asymptotically no larger than the lattice grid-horizon value for a compactly
supported bounded continuous reward. -/
theorem eventually_grid_value_ge_brownian_of_compact_support
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : Continuum.IsBrownian d a B PB)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (hsupp : ∀ s z, z ∉ K → G s z = 0)
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Continuum.brownianDiscount B PB (fun s z => -G s z) T ≤
      stoppingSup ⌊R n ^ 2 * (T : ℝ)⌋₊ (q n) (fun k X =>
        G (((⌊R n ^ 2 * (T : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) + ε := by
  obtain ⟨B', hBm, hBc, hBB', hB'⟩ := exists_continuous_sandpile_brownian_version hB
  let V : ℝ≥0 → ΩB → Continuum.Space d := fun t ω => B' t ω - a
  have hVm : ∀ t, Measurable (V t) := fun t => (hBm t).sub_const a
  have hVc : ∀ ω, Continuous fun t => V t ω := fun ω => (hBc ω).sub continuous_const
  obtain ⟨F, hFm, hF, Ω, mΩ, P, hP, W, Y, hWm, hYm, hWlaw, hYlaw, hconv⟩ :=
    exists_centered_walk_brownian_coupling d R q hRpos hR PB V (isBrownianSpace_sub_start hB')
  let Z : ℝ≥0 → Ω → Continuum.Space d := fun t ω => Y ω t
  have hZm : ∀ t, StronglyMeasurable (Z t) := fun t =>
    ((continuous_eval_const t).measurable.comp hYm).stronglyMeasurable
  have hZc : ∀ ω, Continuous fun t => Z t ω := fun ω => (Y ω).continuous
  have hpath : P.map (LatticeProb.pathMap Z hZc) = PB.map (LatticeProb.pathMap V hVc) := by
    have hZ : LatticeProb.pathMap Z hZc = Y := by
      funext ω
      exact ContinuousMap.ext fun _ => rfl
    have hF' : F =ᵐ[PB] LatticeProb.pathMap V hVc := by
      filter_upwards [hF] with ω hω
      exact ContinuousMap.ext fun t => hω t
    rw [hZ, hYlaw, Measure.map_congr hF']
  let H : ℝ → Continuum.Space d → ℝ := fun s z => G s (z + a)
  have hHc : Continuous (fun p : ℝ × Continuum.Space d => H p.1 p.2) :=
    hGc.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  have hlaw := brownianDiscount_eq_of_path_law_eq P PB Z V hZm
    (fun t => (hVm t).stronglyMeasurable) hZc hVc hpath T H hHc M (fun s z => hG _ _)
  have hval : Continuum.brownianDiscount V PB (fun s z => -H s z) T =
      Continuum.brownianDiscount B' PB (fun s z => -G s z) T := by
    unfold Continuum.brownianDiscount
    congr 1
    ext r
    simp only [Set.mem_ofPred_eq, neg_neg, V, H,
      isBrownianStopping_sub_const_iff, sub_add_cancel]
  have hnat : sSup (naturalStoppingPayoffs P Z T (fun t z => H ((T : ℝ) - t) z)) =
      Continuum.brownianDiscount Z P (fun s z => -H s z) T := by
    unfold Continuum.brownianDiscount
    congr 1
    ext r
    simp only [naturalStoppingPayoffs, Set.mem_ofPred_eq,
      neg_neg, NNReal.coe_le_coe]
  have hlower := eventually_grid_value_ge_limit_of_start_tendsto P R q hRpos hR
    W Y hWm hYm hWlaw hconv T a hstart G hGc K hK hsupp M hG ε hε
  change ∀ᶠ n in atTop, sSup (naturalStoppingPayoffs P Z T
    (fun t z => H ((T : ℝ) - t) z)) ≤ _ at hlower
  rw [hnat, hlaw, hval,
    ← brownianDiscount_eq_of_indistinguishable hB hB' hBB' T G hGc M hG] at hlower
  exact hlower

end Sandpile.External.Stopping
