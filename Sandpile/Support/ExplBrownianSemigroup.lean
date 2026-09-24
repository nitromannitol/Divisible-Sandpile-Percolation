/-
Brownian transition expectations and backward semigroup martingales.

The product law at a deterministic stopping time extends the strong Markov
restart identity to an integrable terminal observable. A field satisfying the
backward semigroup identity is therefore a martingale along the motion, stopped
at its deterministic horizon. The Brownian corollary constructs the restart from
continuous paths and strongly measurable time slices.

The field semigroup identity is an explicit hypothesis. For Gaussian heat
increments it must be proved on a common event for all time-space parameters;
coordinatewise stochastic Fubini alone is insufficient for that assertion.
-/
import Sandpile.Support.ExplOptionalSampling
import Sandpile.Support.ExplBallExit

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

namespace Sandpile.Support

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem setIntegral_transition_of_restart [IsProbabilityMeasure P] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (h : HasStrongMarkovRestart B P 𝔽)
    (s u : ℝ≥0) (hsu : s ≤ u) {E : Set Ω} (hE : MeasurableSet[𝔽 s] E)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f)
    (hi : Integrable (fun ω => f (B u ω)) P) :
    (∫ ω in E, f (B u ω) ∂P) =
      ∫ ω in E, (∫ b, f (B s ω + (B (u - s) b - B 0 b)) ∂P) ∂P := by
  have hm (r : ℝ≥0) : Measurable (B r) := h.adapted.stronglyMeasurable.measurable
  have hs : IsStoppingTime 𝔽 (fun _ : Ω => (s : ℝ≥0∞)) := isStoppingTime_const 𝔽 s
  have hshift : Measurable (fun ω (r : ℝ≥0) => B (s + r) ω - B s ω) :=
    measurable_pi_lambda _ fun r => (hm (s + r)).sub (hm s)
  have hshift0 : Measurable (fun ω (r : ℝ≥0) => B r ω - B 0 ω) :=
    measurable_pi_lambda _ fun r => (hm r).sub (hm 0)
  have hY : Measurable[hs.measurableSpace] (B s) := by
    have hsc : hs.measurableSpace = 𝔽 s := IsStoppingTime.measurableSpace_const 𝔽 s
    rw [hsc]
    exact (h.adapted s).measurable
  have hEs : MeasurableSet[hs.measurableSpace] E := by
    have hsc : hs.measurableSpace = 𝔽 s := IsStoppingTime.measurableSpace_const 𝔽 s
    rw [hsc]
    exact hE
  let F (p : EuclideanSpace ℝ (Fin d) × (ℝ≥0 → EuclideanSpace ℝ (Fin d))) :=
    f (p.1 + p.2 (u - s))
  have hFm : Measurable F :=
    hf.comp (measurable_fst.add ((measurable_pi_apply (u - s)).comp measurable_snd))
  have he (ω : Ω) : F (B s ω, fun r => B (s + r) ω - B s ω) = f (B u ω) := by
    dsimp only [F]
    rw [add_tsub_cancel_of_le hsu, add_sub_cancel]
  have hpair : Measurable (fun ω => (B s ω, fun r => B (s + r) ω - B s ω)) :=
    (hm s).prodMk hshift
  have hFi : Integrable F ((P.restrict E).map (fun ω =>
      (B s ω, fun r => B (s + r) ω - B s ω))) := by
    apply (integrable_map_measure hFm.aestronglyMeasurable hpair.aemeasurable).mpr
    simpa only [Function.comp_def, he, IntegrableOn] using hi.integrableOn (s := E)
  rw [h.map_prod hs hshift hshift0 hY hEs] at hFi
  have hr := setIntegral_restart_of_integrable h hs hshift hshift0 hY hEs hFm hFi
  have hemap (y : EuclideanSpace ℝ (Fin d)) :
      (∫ p, F (y, p) ∂(P.map (fun b (r : ℝ≥0) => B r b - B 0 b))) =
        ∫ b, f (y + (B (u - s) b - B 0 b)) ∂P :=
    integral_map hshift0.aemeasurable
      ((hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  simpa only [he, hemap] using hr


theorem backward_semigroup_martingale [IsProbabilityMeasure P] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (h : HasStrongMarkovRestart B P 𝔽)
    (H : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ) (hH : ∀ r, Measurable (H r))
    (t : ℝ≥0) (hI : ∀ r, r ≤ t → Integrable (fun ω => H (t - r) (B r ω)) P)
    (hS : ∀ r u : ℝ≥0, r ≤ u → u ≤ t → ∀ x,
      (∫ b, H (t - u) (x + (B (u - r) b - B 0 b)) ∂P) = H (t - r) x) :
    Martingale (fun r ω => H (t - min r t) (B (min r t) ω)) 𝔽 P := by
  let M (r : ℝ≥0) (ω : Ω) := H (t - min r t) (B (min r t) ω)
  have hMa : StronglyAdapted 𝔽 M := by
    intro r
    exact ((hH _).comp (h.adapted (min r t)).measurable).stronglyMeasurable.mono
      (𝔽.mono (min_le_left _ _))
  have hMi (r : ℝ≥0) : Integrable (M r) P := hI (min r t) (min_le_right _ _)
  refine ⟨hMa, fun i j hij => ?_⟩
  apply EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝔽.le i) (hMi j)
    (fun E _ _ => (hMi i).integrableOn) ?_ (hMa i).aestronglyMeasurable
  intro E hE _
  by_cases hi : t ≤ i
  · have hj : t ≤ j := hi.trans hij
    simp only [min_eq_right hi, min_eq_right hj]
  · have hit : i ≤ t := (lt_of_not_ge hi).le
    have hijt : i ≤ min j t := le_min hij hit
    have hr := setIntegral_transition_of_restart h i (min j t) hijt hE (H (t - min j t))
      (hH _) (hMi j)
    have he : (∫ ω in E, M j ω ∂P) = ∫ ω in E, M i ω ∂P := by
      simpa only [M, min_eq_left hit, hS i (min j t) hijt (min_le_right _ _)] using hr
    exact he.symm


theorem brownian_backward_semigroup_martingale [IsProbabilityMeasure P] {d : ℕ}
    {x : Sandpile.Continuum.Space d} {B : ℝ≥0 → Ω → Sandpile.Continuum.Space d}
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ r, StronglyMeasurable (B r)) (hBc : ∀ ω, Continuous fun r => B r ω)
    (H : ℝ≥0 → Sandpile.Continuum.Space d → ℝ) (hH : ∀ r, Measurable (H r))
    (t : ℝ≥0) (hI : ∀ r, r ≤ t → Integrable (fun ω => H (t - r) (B r ω)) P)
    (hS : ∀ r u : ℝ≥0, r ≤ u → u ≤ t → ∀ z,
      (∫ b, H (t - u) (z + (B (u - r) b - B 0 b)) ∂P) = H (t - r) z) :
    Martingale (fun r ω => H (t - min r t) (B (min r t) ω)) (natFiltration B hBm) P := by
  exact backward_semigroup_martingale
    ((Sandpile.Continuum.isBrownianSpace_of_isBrownian hB).hasStrongMarkovRestart hBm hBc)
    H hH t hI hS

end Sandpile.Support
