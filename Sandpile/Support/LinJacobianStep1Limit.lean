/-
Step 1 of `lem:dgt4-linearization-from-survival` (`eq:dgt4-derivative-variance-limit`,
`sandpile.tex:5710-5783`) assembled from its early and late halves.

The paper fixes `δ ∈ (0,T)` and splits the time sum of `eq:odometer-derivative`
at `n_R-δR²`.  The early times are those the covariance hypothesis covers and
the late times are the remaining at most `δR²+1` of them.  The late half is
bounded here from `eq:dgt4-tested-cell-l2` and the contraction bound; the early
half is the hypothesis `hearly`, which is `eq:dgt4-early-derivative-variance`.
-/
import Sandpile.Support.LinJacobianStep1

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The early times of `sandpile.tex:5715-5719`: the `i < n` with
`i ≤ n - δR²`. -/
noncomputable def earlyTimes (n : ℕ) (δ R : ℝ) : Finset ℕ :=
  (Finset.range n).filter fun i => (i : ℝ) ≤ (n : ℝ) - δ * R ^ 2

/-- The late times: the remaining `i < n`. -/
noncomputable def lateTimes (n : ℕ) (δ R : ℝ) : Finset ℕ :=
  (Finset.range n).filter fun i => ¬((i : ℝ) ≤ (n : ℝ) - δ * R ^ 2)

theorem earlyTimes_disjoint_lateTimes (n : ℕ) (δ R : ℝ) :
    Disjoint (earlyTimes n δ R) (lateTimes n δ R) := by
  classical
  exact Finset.disjoint_filter_filter_not _ _ _

theorem earlyTimes_union_lateTimes (n : ℕ) (δ R : ℝ) :
    earlyTimes n δ R ∪ lateTimes n δ R = Finset.range n := by
  classical
  exact Finset.filter_union_filter_not_eq _ _

theorem mem_earlyTimes (n : ℕ) (δ R : ℝ) {i : ℕ} (hi : i ∈ earlyTimes n δ R) :
    (i : ℝ) ≤ (n : ℝ) - δ * R ^ 2 := by
  classical
  exact (Finset.mem_filter.1 hi).2

/-- The late times number at most `δR²+1`. -/
theorem card_lateTimes_le (n : ℕ) (δ R : ℝ) (hδ : 0 ≤ δ * R ^ 2) :
    ((lateTimes n δ R).card : ℝ) ≤ δ * R ^ 2 + 1 := by
  classical
  set k : ℕ := ⌈δ * R ^ 2⌉₊ with hk
  have hsub : lateTimes n δ R ⊆ Finset.Ico (n - k) n := by
    intro i hi
    rw [lateTimes, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hin, hlt⟩ := hi
    rw [Finset.mem_Ico]
    refine ⟨?_, hin⟩
    by_contra hcon
    push Not at hcon
    have hik : i + k < n := by omega
    have hcast : (i : ℝ) + (k : ℝ) < (n : ℝ) := by exact_mod_cast hik
    have hceil : δ * R ^ 2 ≤ (k : ℝ) := Nat.le_ceil _
    exact hlt (by linarith)
  have hcard := Finset.card_le_card hsub
  have hIco : (Finset.Ico (n - k) n).card = n - (n - k) := Nat.card_Ico _ _
  have hfinal : (lateTimes n δ R).card ≤ k := by omega
  have hcast2 : ((lateTimes n δ R).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hfinal
  have hceil2 : (k : ℝ) < δ * R ^ 2 + 1 := Nat.ceil_lt_add_one hδ
  linarith

variable [NeZero d] (μ : Measure (Site d → ℝ))

/-- The site sum of the second moments of the late part, bounded as in
`eq:dgt4-late-derivative-variance`. -/
theorem tsum_integral_sq_sum_jacobianTimes_le [IsProbabilityMeasure μ] (hd : 1 ≤ d) (n : ℕ)
    (s : Finset (Site d)) (a : Site d → ℝ) (ha : ∀ x, 0 ≤ a x) (hsupp : ∀ x ∉ s, a x = 0)
    (hsq : Summable fun z : Site d => (a z) ^ 2) (t : Finset ℕ) :
    (∑' z : Site d, ∫ σ, (∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z) ^ 2 ∂μ)
      ≤ (t.card : ℝ) ^ 2 * ∑' z : Site d, (a z) ^ 2 := by
  have hle : ∀ z : Site d,
      (∫ σ, (∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z) ^ 2 ∂μ)
        ≤ (∑ i ∈ t, (avg^[i] a) z) ^ 2 := fun z =>
    integral_sq_le_of_le μ _ _ (memLp_sum_jacobianTimes μ n s a ha t z)
      (fun σ => sum_a_jacobianTimes_nonneg s a ha _ n t z)
      (fun σ => sum_a_jacobianTimes_le hd s a ha hsupp _ n t z)
  exact (Summable.tsum_le_tsum hle
      (summable_integral_sq_sum_jacobianTimes μ hd n s a ha hsupp hsq t)
      (summable_sq_sum_iterate_avg hd hsq t)).trans
    (tsum_sq_sum_iterate_avg_le hd hsq t)

/-- **Step 1 of `lem:dgt4-linearization-from-survival`**
(`eq:dgt4-derivative-variance-limit`, `sandpile.tex:5705-5778`): if the early
half obeys `eq:dgt4-early-derivative-variance` and the late half obeys
`eq:dgt4-late-derivative-variance`, the site sum of the variances of the
coordinate derivative of the tested field tends to zero. -/
theorem tendsto_tsum_variance_odometerJacobian {l : Filter ℝ} [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (n : ℝ → ℕ) (s : ℝ → Finset (Site d)) (a : ℝ → Site d → ℝ)
    (ha : ∀ (R : ℝ) (x : Site d), 0 ≤ a R x)
    (hsupp : ∀ (R : ℝ), ∀ x ∉ s R, a R x = 0)
    (hsq : ∀ R : ℝ, Summable fun z : Site d => (a R z) ^ 2)
    (C : ℝ) (hC : 0 ≤ C) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hearly : ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ eps : ℝ → ℝ, Tendsto eps l (𝓝 0) ∧
      ∀ᶠ R : ℝ in l, (∑' z : Site d, variance
          (fun σ => ∑ x ∈ s R, a R x *
            jacobianTimes (scenery d σ) (n R) (earlyTimes (n R) δ R) x z) μ)
        ≤ C * eps R + C / (δ * R ^ 2))
    (hlate : ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ o : ℝ → ℝ, Tendsto o l (𝓝 0) ∧
      ∀ᶠ R : ℝ in l, ((lateTimes (n R) δ R).card : ℝ) ^ 2 *
          (∑' z : Site d, (a R z) ^ 2) ≤ C * δ ^ 2 + o R)
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto (fun R : ℝ => ∑' z : Site d,
        variance (fun σ => ∑ x ∈ s R, a R x * odometerJacobian (scenery d σ) (n R) x z) μ)
      l (𝓝 0) := by
  classical
  set V : ℝ → ℝ := fun R => ∑' z : Site d,
    variance (fun σ => ∑ x ∈ s R, a R x * odometerJacobian (scenery d σ) (n R) x z) μ with hV
  set early : ℝ → ℝ → ℝ := fun δ R => ∑' z : Site d, variance
    (fun σ => ∑ x ∈ s R, a R x *
      jacobianTimes (scenery d σ) (n R) (earlyTimes (n R) δ R) x z) μ with hearlydef
  set late : ℝ → ℝ → ℝ := fun δ R => ∑' z : Site d,
    ∫ σ, (∑ x ∈ s R, a R x *
      jacobianTimes (scenery d σ) (n R) (lateTimes (n R) δ R) x z) ^ 2 ∂μ with hlatedef
  have hjac : ∀ (R : ℝ) (δ : ℝ) (σ : Site d → ℝ) (z : Site d),
      (∑ x ∈ s R, a R x * odometerJacobian (scenery d σ) (n R) x z)
        = ∑ x ∈ s R, a R x *
            jacobianTimes (scenery d σ) (n R)
              (earlyTimes (n R) δ R ∪ lateTimes (n R) δ R) x z := by
    intro R δ σ z
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [earlyTimes_union_lateTimes, jacobianTimes_range hd]
  refine tendsto_zero_of_delta_split (hl := hl) V early late C hC δ₀ hδ₀
    (Filter.Eventually.of_forall fun R => tsum_nonneg fun z => variance_nonneg _ _)
    (fun δ hδ _ => Filter.Eventually.of_forall fun R => ?_) hearly ?_
  · have hrw : V R = ∑' z : Site d, variance
        (fun σ => ∑ x ∈ s R, a R x * jacobianTimes (scenery d σ) (n R)
          (earlyTimes (n R) δ R ∪ lateTimes (n R) δ R) x z) μ := by
      refine tsum_congr fun z => congrArg (fun f => variance f μ) (funext fun σ => ?_)
      exact hjac R δ σ z
    rw [hrw]
    exact tsum_variance_split μ hd (n R) (s R) (a R) (ha R) (hsupp R) (hsq R)
      (earlyTimes_disjoint_lateTimes (n R) δ R)
  · intro δ hδ hδlt
    obtain ⟨o, hotend, hobd⟩ := hlate δ hδ hδlt
    refine ⟨o, hotend, ?_⟩
    filter_upwards [hobd] with R hR
    exact (tsum_integral_sq_sum_jacobianTimes_le μ hd (n R) (s R) (a R) (ha R) (hsupp R)
      (hsq R) (lateTimes (n R) δ R)).trans hR

end Sandpile
