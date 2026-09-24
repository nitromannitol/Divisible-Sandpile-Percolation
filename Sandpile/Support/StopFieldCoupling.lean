/-
Couplings of random fields that are uniformly close on a compact set.
Finite-dimensional convergence, equicontinuity in probability, and almost-sure
continuity of the limit suffice, with outer-measure control of the discrepancy.
-/
import Sandpile.Support.StopWeakCoupling
import Sandpile.Support.StopPathSpace

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

theorem Sandpile.Continuum.exists_net_close_in_probability
    {E : Type*} [MetricSpace E] [CompactSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → E → ℝ) (hg : ∀ x, AEMeasurable (fun ω => g ω x) P)
    (hc : ∀ᵐ ω ∂P, Continuous (g ω))
    (η₀ ε δ : ℝ) (hη₀ : 0 < η₀) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (m : ℕ) (x : Fin m → E) (η : ℝ), 0 < η ∧ η ≤ η₀ ∧
      (∀ y ∈ (univ : Set E), ∃ k, dist (x k) y < η) ∧
      P {ω | ∃ y : E, ε < |LatticeProb.netApprox x η (fun k => g ω (x k)) y - g ω y|}
        ≤ ENNReal.ofReal δ := by
  classical
  borelize C(E, ℝ)
  let r : ℕ → ℝ := fun n => η₀ / (n + 1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  have hrle : ∀ n, r n ≤ η₀ := by
    intro n
    apply div_le_self hη₀.le
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  choose m x hx hnet using fun n =>
    LatticeProb.exists_net (isCompact_univ : IsCompact (univ : Set E)) (hr n)
  let F : ℕ → Ω → C(E, ℝ) := fun n ω =>
    ⟨LatticeProb.netApprox (x n) (r n) (fun k => g ω (x n k)),
      continuousOn_univ.mp (LatticeProb.continuousOn_netApprox _ (hnet n))⟩
  let G : Ω → C(E, ℝ) := fun ω => ContinuousMap.mkD (g ω) 0
  have hF : ∀ n, AEMeasurable (F n) P := by
    intro n
    exact (Sandpile.Continuum.lipschitz_net_continuousMap (x n) (r n) (hnet n)).continuous.measurable
      |>.comp_aemeasurable (aemeasurable_pi_lambda _ fun k => hg (x n k))
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hc] with ω hω
    have hr0 : Tendsto r atTop (𝓝 0) := by
      simpa only [r, div_eq_mul_inv, one_mul, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul η₀
    have h := Sandpile.Continuum.tendsto_net_continuousMap (ContinuousMap.mkD (g ω) 0)
      m x r hnet hr0
    simpa only [F, G, ContinuousMap.mkD_apply_of_continuous hω] using h
  have hprob := tendstoInMeasure_of_tendsto_ae (fun n => (hF n).aestronglyMeasurable) hlim
  have hmeas := tendstoInMeasure_iff_dist.mp hprob ε hε
  obtain ⟨N, hN⟩ := (hmeas.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))).exists
  refine ⟨m N, x N, r N, hr N, hrle N, hnet N, ?_⟩
  apply le_trans (measure_mono_ae ?_) hN.le
  filter_upwards [hc] with ω hω
  rintro ⟨y, hy⟩
  change ε ≤ dist (F N ω) (G ω)
  have hd := ContinuousMap.dist_apply_le_dist (f := F N ω) (g := G ω) y
  simp only [F, G, ContinuousMap.coe_mk, ContinuousMap.mkD_apply_of_continuous hω,
    Real.dist_eq] at hd
  exact hy.le.trans hd

theorem Sandpile.Continuum.exists_field_coupling_on_compact
    {ι E : Type*} [MetricSpace E] [CompactSpace E]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    (μ : (i : ι) → Measure (Ω i)) (ν : Measure Ω')
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (f : (i : ι) → Ω i → E → ℝ) (g : Ω' → E → ℝ)
    (hg : ∀ x, AEMeasurable (fun ω => g ω x) ν)
    (hc : ∀ᵐ ω ∂ν, Continuous (g ω)) (L : Filter ι)
    (hfdd : ∀ (m : ℕ) (x : Fin m → E), TendstoInDistribution
      (fun i ω k => f i ω (x k)) L (fun ω k => g ω (x k)) μ ν)
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ i in L,
      μ i {ω | ∃ x y : E, dist x y < ρ ∧ η < |f i ω x - f i ω y|} ≤ ENNReal.ofReal ε)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ i in L, ∃ P : Measure (Ω i × Ω'), IsProbabilityMeasure P ∧
      P.map Prod.fst = μ i ∧ P.map Prod.snd = ν ∧
      P {p | ∃ x : E, ε < |f i p.1 x - g p.2 x|} ≤ ENNReal.ofReal δ := by
  classical
  obtain ⟨ρ, hρ, hsource⟩ := htight (δ / 3) (ε / 3) (by positivity) (by positivity)
  obtain ⟨m, x, η, hη, hηρ, hnet, hlimit⟩ :=
    Sandpile.Continuum.exists_net_close_in_probability ν g hg hc ρ (ε / 3) (δ / 3)
      hρ (by positivity) (by positivity)
  have hcouple := Sandpile.Continuum.exists_coupling_close_of_tendstoInDistribution_ae μ ν
    (fun i ω k => f i ω (x k)) (fun ω k => g ω (x k)) L (hfdd m x)
    (ε / 3) (δ / 3) (by positivity) (by positivity)
  filter_upwards [hsource, hcouple] with i hi hcoup
  obtain ⟨P, hP, hPf, hPs, hfinite⟩ := hcoup
  let badF : Set (Ω i) := {ω | ∃ z y : E, dist z y < ρ ∧ ε / 3 < |f i ω z - f i ω y|}
  let badG : Set Ω' := {ω | ∃ y : E,
    ε / 3 < |LatticeProb.netApprox x η (fun k => g ω (x k)) y - g ω y|}
  let badNet : Set (Ω i × Ω') := {p | ε / 3 <
    dist (fun k : Fin m => f i p.1 (x k)) (fun k : Fin m => g p.2 (x k))}
  let bad : Set (Ω i × Ω') := {p | ∃ y : E, ε < |f i p.1 y - g p.2 y|}
  have hsub : bad ⊆ (Prod.fst ⁻¹' badF) ∪ badNet ∪ (Prod.snd ⁻¹' badG) := by
    intro p hp
    by_cases hFbad : p.1 ∈ badF
    · exact Or.inl (Or.inl hFbad)
    by_cases hNbad : p ∈ badNet
    · exact Or.inl (Or.inr hNbad)
    by_cases hGbad : p.2 ∈ badG
    · exact Or.inr hGbad
    exfalso
    obtain ⟨y, hy⟩ := hp
    have hdist : dist (fun k : Fin m => f i p.1 (x k))
        (fun k : Fin m => g p.2 (x k)) ≤ ε / 3 := le_of_not_gt hNbad
    have hcoeff : ∀ k : Fin m, |f i p.1 (x k) - g p.2 (x k)| ≤ ε / 3 := by
      intro k
      have hk := dist_le_pi_dist (fun k : Fin m => f i p.1 (x k))
        (fun k : Fin m => g p.2 (x k)) k
      rw [Real.dist_eq] at hk
      exact hk.trans hdist
    have h1 : |LatticeProb.netApprox x η (fun k => f i p.1 (x k)) y - f i p.1 y| ≤ ε / 3 := by
      apply LatticeProb.abs_netApprox_sub_le (LatticeProb.tentSum_pos (hnet y (mem_univ y)))
      intro k hk
      exact le_of_not_gt (fun h => hFbad ⟨x k, y, hk.trans_le hηρ, h⟩)
    have h2 : |LatticeProb.netApprox x η (fun k => f i p.1 (x k)) y -
        LatticeProb.netApprox x η (fun k => g p.2 (x k)) y| ≤ ε / 3 :=
      LatticeProb.abs_netApprox_sub_netApprox_le (LatticeProb.tentSum_pos (hnet y (mem_univ y))) hcoeff
    have h3 : |LatticeProb.netApprox x η (fun k => g p.2 (x k)) y - g p.2 y| ≤ ε / 3 :=
      le_of_not_gt (fun h => hGbad ⟨y, h⟩)
    have ha := abs_sub_le (f i p.1 y)
      (LatticeProb.netApprox x η (fun k => f i p.1 (x k)) y) (g p.2 y)
    have hb := abs_sub_le (LatticeProb.netApprox x η (fun k => f i p.1 (x k)) y)
      (LatticeProb.netApprox x η (fun k => g p.2 (x k)) y) (g p.2 y)
    rw [abs_sub_comm] at h1
    linarith
  refine ⟨P, hP, hPf, hPs, ?_⟩
  calc
    P bad ≤ μ i badF + P badNet + ν badG :=
      Sandpile.Continuum.measure_error_le_of_marginals (μ i) ν P hPf hPs badF badG badNet bad hsub
    _ ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) :=
      add_le_add (add_le_add hi hfinite) hlimit
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
