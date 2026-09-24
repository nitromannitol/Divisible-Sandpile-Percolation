/-
Finite-net approximations of continuous fields on a compact metric space.
The interpolants are Lipschitz functions of their coefficients and converge
uniformly to each continuous field.
-/
import LatticeProb.Prob.FddTight

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

theorem Sandpile.Continuum.lipschitz_net_continuousMap
    {E : Type*} [MetricSpace E] [CompactSpace E]
    {m : ℕ} (x : Fin m → E) (η : ℝ)
    (hnet : ∀ y ∈ (univ : Set E), ∃ k, dist (x k) y < η) :
    LipschitzWith 1 (fun u : Fin m → ℝ =>
      (⟨LatticeProb.netApprox x η u,
        continuousOn_univ.mp (LatticeProb.continuousOn_netApprox u hnet)⟩ : C(E, ℝ)))  := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [NNReal.coe_one, one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro y
  rw [Real.dist_eq]
  exact LatticeProb.abs_netApprox_sub_netApprox_le
    (LatticeProb.tentSum_pos (hnet y (mem_univ y)))
    (fun k => by simpa only [Real.dist_eq] using dist_le_pi_dist u v k)

theorem Sandpile.Continuum.tendsto_net_continuousMap
    {E : Type*} [MetricSpace E] [CompactSpace E]
    (v : C(E, ℝ)) (m : ℕ → ℕ) (x : (n : ℕ) → Fin (m n) → E) (r : ℕ → ℝ)
    (hnet : ∀ n, ∀ y ∈ (univ : Set E), ∃ k, dist (x n k) y < r n)
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n =>
      (⟨LatticeProb.netApprox (x n) (r n) (fun k => v (x n k)),
        continuousOn_univ.mp (LatticeProb.continuousOn_netApprox _ (hnet n))⟩ : C(E, ℝ)))
      atTop (𝓝 v) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨η, hη, huc⟩ :=
    (Metric.uniformContinuousOn_iff.1
      (isCompact_univ.uniformContinuousOn_of_continuous v.continuous.continuousOn))
      (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hr η hη
  refine ⟨N, fun n hn => ?_⟩
  have hrn : r n < η := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  apply lt_of_le_of_lt ((ContinuousMap.dist_le (show 0 ≤ ε / 2 by positivity)).mpr ?_)
    (by linarith)
  intro y
  rw [Real.dist_eq]
  apply LatticeProb.abs_netApprox_sub_le (LatticeProb.tentSum_pos (hnet n y (mem_univ y)))
  intro k hk
  have he := huc (x n k) (mem_univ _) y (mem_univ _) (hk.trans hrn)
  simpa only [Real.dist_eq] using he.le

theorem Sandpile.Continuum.aemeasurable_continuousMap_mkD
    {E : Type*} [MetricSpace E] [CompactSpace E]
    [MeasurableSpace C(E, ℝ)] [BorelSpace C(E, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → E → ℝ)
    (hf : ∀ x, AEMeasurable (fun ω => f ω x) P)
    (hc : ∀ᵐ ω ∂P, Continuous (f ω)) :
    AEMeasurable (fun ω => ContinuousMap.mkD (f ω) 0) P := by
  classical
  let r : ℕ → ℝ := fun n => 1 / (n + 1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  choose m x hx hnet using fun n => LatticeProb.exists_net (isCompact_univ : IsCompact (univ : Set E)) (hr n)
  let F : ℕ → Ω → C(E, ℝ) := fun n ω =>
    ⟨LatticeProb.netApprox (x n) (r n) (fun k => f ω (x n k)),
      continuousOn_univ.mp (LatticeProb.continuousOn_netApprox _ (hnet n))⟩
  have hF : ∀ n, AEMeasurable (F n) P := by
    intro n
    exact (Sandpile.Continuum.lipschitz_net_continuousMap (x n) (r n) (hnet n)).continuous.measurable
      |>.comp_aemeasurable (aemeasurable_pi_lambda _ fun k => hf (x n k))
  refine aemeasurable_of_tendsto_metrizable_ae atTop hF ?_
  filter_upwards [hc] with ω hω
  have h := Sandpile.Continuum.tendsto_net_continuousMap (ContinuousMap.mkD (f ω) 0)
    m x r hnet (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [F, ContinuousMap.mkD_apply_of_continuous hω] using h
