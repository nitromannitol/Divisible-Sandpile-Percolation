import Sandpile.External.Stopping.StoppingValueLaw
import Sandpile.External.Stopping.BrownianContinuousVersion
import Sandpile.External.Stopping.WalkBrownianInvariance

/-!
# Brownian stopping values and realization

Finite-horizon bounded continuous stopping values of Brownian motion depend on
the starting point and the reward, not on the realization of the motion.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Centering a sandpile Brownian motion gives a motion started at the origin. -/
theorem isBrownianSpace_sub_start
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {x : Continuum.Space d} {B : ℝ≥0 → Ω → Continuum.Space d}
    (hB : Continuum.IsBrownian d x B P) :
    LatticeProb.IsBrownianSpace d 0 (fun t ω => B t ω - x) P where
  start := by
    filter_upwards [hB.start] with ω hω
    simp only [hω, sub_self]
  coord := by
    intro i
    simpa only [PiLp.sub_apply, PiLp.zero_apply, sub_zero] using hB.coord i
  indep := by
    have h := hB.indep.comp (fun (i : Fin d) (f : ℝ≥0 → ℝ) (t : ℝ≥0) => f t - x i)
      (fun i => Measurable.of_eval fun t =>
        (measurable_pi_apply t : Measurable (fun f : ℝ≥0 → ℝ => f t)).sub_const (x i))
    convert h using 1
    funext i ω t
    simp only [Function.comp_apply, PiLp.sub_apply]

/-- Continuous sandpile Brownian motions with the same starting point have the
same path law. -/
theorem map_pathMap_eq_of_sandpile_brownian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C Q)
    (_hBm : ∀ t, Measurable (B t)) (_hCm : ∀ t, Measurable (C t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hCc : ∀ ω, Continuous fun t => C t ω) :
    P.map (LatticeProb.pathMap B hBc) = Q.map (LatticeProb.pathMap C hCc) := by
  let R : ℕ → ℝ := fun n => n
  have hR : Tendsto R atTop atTop := by
    exact tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun n => Lclt.scaledSite (R n) (0 : Site d)) atTop (𝓝 0) := by
    have hz (n : ℕ) : Lclt.scaledSite (R n) (0 : Site d) = 0 := by
      ext i
      simp [Lclt.scaledSite]
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Continuum.Space d)) atTop (𝓝 0))
  let B₀ : ℝ≥0 → Ω → Continuum.Space d := fun t ω => B t ω - x
  let C₀ : ℝ≥0 → Ω' → Continuum.Space d := fun t ω => C t ω - x
  obtain ⟨F, hFm, hFae, hFlim⟩ := exists_brownian_path_limit d R (fun _ => 0) hR 0 hx
    P B₀ (isBrownianSpace_sub_start hB)
  obtain ⟨H, hHm, hHae, hHlim⟩ := exists_brownian_path_limit d R (fun _ => 0) hR 0 hx
    Q C₀ (isBrownianSpace_sub_start hC)
  have heq : P.map F = Q.map H := by
    have hh := tendsto_nhds_unique hFlim hHlim
    exact congrArg ProbabilityMeasure.toMeasure hh
  let addx : C(ℝ≥0, Continuum.Space d) → C(ℝ≥0, Continuum.Space d) :=
    fun f => ContinuousMap.const _ x + f
  have hX : Measurable addx := by
    exact ((continuous_const : Continuous (fun _ : C(ℝ≥0, Continuum.Space d) =>
      ContinuousMap.const _ x)).add continuous_id).measurable
  have hBF : (fun ω => LatticeProb.pathMap B hBc ω) =ᵐ[P] fun ω => addx (F ω) := by
    filter_upwards [hFae] with ω hω
    apply ContinuousMap.ext
    intro t
    change B t ω = x + F ω t
    rw [hω t]
    simp only [zero_add, B₀, add_sub_cancel]
  have hCH : (fun ω => LatticeProb.pathMap C hCc ω) =ᵐ[Q] fun ω => addx (H ω) := by
    filter_upwards [hHae] with ω hω
    apply ContinuousMap.ext
    intro t
    change C t ω = x + H ω t
    rw [hω t]
    simp only [zero_add, C₀, add_sub_cancel]
  rw [Measure.map_congr hBF, Measure.map_congr hCH]
  change P.map (addx ∘ F) = Q.map (addx ∘ H)
  rw [← Measure.map_map hX hFm, ← Measure.map_map hX hHm, heq]

/-- Bounded continuous Brownian stopping values are independent of the
underlying probability space and of the chosen Brownian realization. -/
theorem brownianDiscount_eq_of_isBrownian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C Q)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuum.brownianDiscount B P (fun s z => -G s z) T =
      Continuum.brownianDiscount C Q (fun s z => -G s z) T := by
  obtain ⟨B', hB'm, hB'c, hBB', hB'⟩ := exists_continuous_sandpile_brownian_version hB
  obtain ⟨C', hC'm, hC'c, hCC', hC'⟩ := exists_continuous_sandpile_brownian_version hC
  rw [brownianDiscount_eq_of_indistinguishable hB hB' hBB' T G hGc M hG,
    brownianDiscount_eq_of_indistinguishable hC hC' hCC' T G hGc M hG]
  exact brownianDiscount_eq_of_path_law_eq P Q B' C'
    (fun t => (hB'm t).stronglyMeasurable) (fun t => (hC'm t).stronglyMeasurable) hB'c hC'c
    (map_pathMap_eq_of_sandpile_brownian P Q x B' C' hB' hC' hB'm hC'm hB'c hC'c)
    T G hGc M hG

end Sandpile.External.Stopping
