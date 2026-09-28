import Sandpile.Support.LinSurvivalMeas

/-! # Early Variance Fubini

The Fubini and boundedness lemmas behind the expansion identity of
`eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`), the first open
piece of `eq:dgt4-derivative-variance-limit`.

The paper expands `∑_z Var(D^{≤}_{R,z})` over two independent walks.  The steps
that produce the double walk average are Fubini and the boundedness of the
survival indicators:

  `Cov(∫_X f(X,·), ∫_Y g(Y,·)) = ∫_X ∫_Y Cov(f(X,·), g(Y,·))`,
  `∫_b μ[f(b,·)] = μ[∫_b f(b,·)]`,
  `|μ[∫_b H(b,·)]| ≤ C` for `|H| ≤ C`.

The covariance is signed, so these are recorded in the Bochner form.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- If `|H| ≤ C` everywhere and `H` is a.e. strongly measurable under a probability
measure `μ`, then `|∫ H dμ| ≤ C`: the integral of a bounded function against a
probability measure is bounded by the same constant. -/
theorem abs_integral_le_of_bound_simple {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (H : α → ℝ)
    (hHm : AEStronglyMeasurable H μ) (C : ℝ) (hH : ∀ a, |H a| ≤ C) :
    |∫ a, H a ∂μ| ≤ C := by
  refine le_trans (abs_integral_le_integral_abs (μ := μ)) ?_
  have h1 : Integrable (fun a => |H a|) μ :=
    Integrable.of_bound hHm.norm C (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_abs]; exact hH a)
  have h2 : Integrable (fun _ : α => C) μ := integrable_const C
  calc ∫ a, |H a| ∂μ ≤ ∫ _ : α, C ∂μ := integral_mono h1 h2 (fun a => hH a)
    _ = C := by rw [integral_const, probReal_univ, one_smul]

/-- If `H : β → α → ℝ` is jointly measurable and uniformly bounded by `C`, then the
`μ`-mean of the `ν`-integral `b ↦ ∫ H b · dν` is bounded by `C` in absolute value. -/
theorem abs_integral_le_of_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (H : β → α → ℝ)
    (hHm : Measurable (Function.uncurry H)) (C : ℝ) (hH : ∀ b a, |H b a| ≤ C) :
    |μ[fun a => ∫ b, H b a ∂ν]| ≤ C := by
  have hb : ∀ a, |∫ b, H b a ∂ν| ≤ C := by
    intro a
    refine le_trans (abs_integral_le_integral_abs (μ := ν)) ?_
    have h1 : Integrable (fun b => |H b a|) ν :=
      Integrable.of_bound
        ((hHm.comp (by fun_prop : Measurable fun b : β => (b, a))).norm).aestronglyMeasurable
        C (Eventually.of_forall fun b => by
          rw [Real.norm_eq_abs, abs_abs]; exact hH b a)
    have h2 : Integrable (fun _ : β => C) ν := integrable_const C
    calc ∫ b, |H b a| ∂ν ≤ ∫ _ : β, C ∂ν := integral_mono h1 h2 (fun b => hH b a)
      _ = C := by rw [integral_const, probReal_univ, one_smul]
  rw [← Real.norm_eq_abs]
  calc ‖∫ a, (fun a => ∫ b, H b a ∂ν) a ∂μ‖
      ≤ C * μ.real Set.univ := norm_integral_le_of_norm_le_const
        (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hb a)
    _ = C := by rw [probReal_univ, mul_one]

/-- Fubini for the mean of a `ν`-family of `μ`-integrals: with `F` jointly measurable
and uniformly bounded, `∫_b μ[F b ·] dν = μ[a ↦ ∫_b F b a dν]`. -/
theorem integral_mean_eq_mean_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (F : β → α → ℝ) (hF : Measurable (Function.uncurry F)) (C : ℝ)
    (hFb : ∀ b a, |F b a| ≤ C) :
    (∫ b, μ[fun a => F b a] ∂ν) = μ[fun a => ∫ b, F b a ∂ν] := by
  have hFi : ∀ a, Integrable (fun b => F b a) ν := fun a =>
    Integrable.of_bound
      ((hF.comp (by fun_prop : Measurable fun b : β => (b, a))).aestronglyMeasurable)
      C (Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hFb b a)
  have hFb' : ∀ b, Integrable (fun a => F b a) μ := fun b =>
    Integrable.of_bound
      ((hF.comp (by fun_prop : Measurable fun a : α => (b, a))).aestronglyMeasurable)
      C (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hFb b a)
  have hswap := integral_integral_swap (μ := ν) (ν := μ)
    (f := fun b a => F b a) ?_
  · rw [hswap]
  · refine Integrable.mono' (integrable_const C) ?_ ?_
    · exact (hF.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs]; exact hFb p.1 p.2


/-- **The Fubini step of the early variance expansion.**  For jointly measurable,
uniformly bounded `F, G`, the covariance of the `ν`- and `ν₂`-integrals of `F` and
`G` equals the `ν.prod ν₂`-integral of the pointwise covariance, i.e.
`Cov(∫_b F b ·, ∫_b G b ·) = ∫_{b,b'} Cov(F b ·, G b' ·)`. -/
theorem covariance_integral_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν ν₂ : Measure β)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν₂]
    (F G : β → α → ℝ) (hF : Measurable (Function.uncurry F))
    (hG : Measurable (Function.uncurry G)) (C : ℝ)
    (hFb : ∀ b a, |F b a| ≤ C) (hGb : ∀ b a, |G b a| ≤ C) :
    covariance (fun a => ∫ b, F b a ∂ν) (fun a => ∫ b, G b a ∂ν₂) μ
      = ∫ p, covariance (fun a => F p.1 a) (fun a => G p.2 a) μ ∂(ν.prod ν₂) := by
  have hFm : ∀ a, AEStronglyMeasurable (fun b => F b a) ν := fun a =>
    (hF.comp (by fun_prop : Measurable fun b : β => (b, a))).aestronglyMeasurable
  have hGm : ∀ a, AEStronglyMeasurable (fun b => G b a) ν₂ := fun a =>
    (hG.comp (by fun_prop : Measurable fun b : β => (b, a))).aestronglyMeasurable
  have hFi : ∀ a, Integrable (fun b => F b a) ν := fun a =>
    Integrable.of_bound (hFm a) C (Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs]; exact hFb b a)
  have hGi : ∀ a, Integrable (fun b => G b a) ν₂ := fun a =>
    Integrable.of_bound (hGm a) C (Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs]; exact hGb b a)
  have hFint : ∀ a : α, Integrable (fun b => ∫ x, F b x ∂μ) ν := fun _ =>
    Integrable.integral_prod_left (μ := ν) (ν := μ)
      (f := fun p : β × α => F p.1 p.2) (by
        refine Integrable.mono' (integrable_const C) ?_ ?_
        · exact (hF.comp (by fun_prop)).aestronglyMeasurable
        · filter_upwards with p
          rw [Real.norm_eq_abs]; exact hFb p.1 p.2)
  have hGint : ∀ a : α, Integrable (fun b => ∫ x, G b x ∂μ) ν₂ := fun _ =>
    Integrable.integral_prod_left (μ := ν₂) (ν := μ)
      (f := fun p : β × α => G p.1 p.2) (by
        refine Integrable.mono' (integrable_const C) ?_ ?_
        · exact (hG.comp (by fun_prop)).aestronglyMeasurable
        · filter_upwards with p
          rw [Real.norm_eq_abs]; exact hGb p.1 p.2)
  have hmeanF : μ[fun a => ∫ b, F b a ∂ν] = ∫ b, μ[fun a => F b a] ∂ν :=
    (integral_mean_eq_mean_integral μ ν F hF C hFb).symm
  have hmeanG : μ[fun a => ∫ b, G b a ∂ν₂] = ∫ b, μ[fun a => G b a] ∂ν₂ :=
    (integral_mean_eq_mean_integral μ ν₂ G hG C hGb).symm
  have hFc : ∀ a, (∫ b, F b a ∂ν) - μ[fun a => ∫ b, F b a ∂ν]
      = ∫ b, (F b a - μ[fun a => F b a]) ∂ν := fun a => by
    rw [hmeanF]
    exact (integral_sub (hFi a) (hFint a)).symm
  have hGc : ∀ a, (∫ b, G b a ∂ν₂) - μ[fun a => ∫ b, G b a ∂ν₂]
      = ∫ b, (G b a - μ[fun a => G b a]) ∂ν₂ := fun a => by
    rw [hmeanG]
    exact (integral_sub (hGi a) (hGint a)).symm
  have hprod : ∀ a, (∫ b, (F b a - μ[fun a => F b a]) ∂ν)
        * (∫ b, (G b a - μ[fun a => G b a]) ∂ν₂)
      = ∫ p, (F p.1 a - μ[fun a => F p.1 a])
          * (G p.2 a - μ[fun a => G p.2 a]) ∂(ν.prod ν₂) := fun a =>
    (integral_prod_mul (fun b => F b a - μ[fun a => F b a])
      (fun b => G b a - μ[fun a => G b a])).symm
  have hmean : ∀ (H : β → α → ℝ), Measurable (Function.uncurry H) →
      (∀ b a, |H b a| ≤ C) → |μ[fun a => ∫ b, H b a ∂ν]| ≤ C :=
    fun H hHm hH => abs_integral_le_of_bound μ ν H hHm C hH
  have hswap : (∫ a, ∫ p, (F p.1 a - μ[fun a => F p.1 a])
        * (G p.2 a - μ[fun a => G p.2 a]) ∂(ν.prod ν₂) ∂μ)
      = ∫ p, ∫ a, (F p.1 a - μ[fun a => F p.1 a])
        * (G p.2 a - μ[fun a => G p.2 a]) ∂μ ∂(ν.prod ν₂) := by
    refine integral_integral_swap ?_
    refine Integrable.mono' (integrable_const ((2 * C) * (2 * C))) ?_ ?_
    · have hm1 : Measurable (fun q : α × (β × β) => F q.2.1 q.1) := by fun_prop
      have hm2 : Measurable (fun q : α × (β × β) => G q.2.2 q.1) := by fun_prop
      have hm3 : Measurable (fun q : α × (β × β) => μ[fun a => F q.2.1 a]) :=
        (StronglyMeasurable.integral_prod_right (ν := μ)
          (f := fun (q : α × (β × β)) (a : α) => F q.2.1 a) (by fun_prop)).measurable
      have hm4 : Measurable (fun q : α × (β × β) => μ[fun a => G q.2.2 a]) :=
        (StronglyMeasurable.integral_prod_right (ν := μ)
          (f := fun (q : α × (β × β)) (a : α) => G q.2.2 a) (by fun_prop)).measurable
      have hmm : Measurable (fun q : α × (β × β) =>
          (F q.2.1 q.1 - μ[fun a => F q.2.1 a]) * (G q.2.2 q.1 - μ[fun a => G q.2.2 a])) :=
        (hm1.sub hm3).mul (hm2.sub hm4)
      change AEStronglyMeasurable (fun q : α × (β × β) =>
        (F q.2.1 q.1 - ∫ x, F q.2.1 x ∂μ) * (G q.2.2 q.1 - ∫ x, G q.2.2 x ∂μ))
        (μ.prod (ν.prod ν₂))
      exact hmm.aestronglyMeasurable
    · filter_upwards with q
      show |(F q.2.1 q.1 - μ[fun a => F q.2.1 a])
          * (G q.2.2 q.1 - μ[fun a => G q.2.2 a])| ≤ 2 * C * (2 * C)
      rw [abs_mul]
      have h1 : |F q.2.1 q.1 - μ[fun a => F q.2.1 a]| ≤ 2 * C := by
        rw [abs_sub_le_iff]
        have hm := abs_le.mp (abs_integral_le_of_bound_simple μ (fun a : α => F q.2.1 a)
          ((hF.comp (by fun_prop : Measurable fun a : α => (q.2.1, a))).aestronglyMeasurable)
          C (fun a => hFb q.2.1 a))
        have hFq := abs_le.mp (hFb q.2.1 q.1)
        exact ⟨by linarith [hm.1, hFq.2], by linarith [hm.2, hFq.1]⟩
      have h2 : |G q.2.2 q.1 - μ[fun a => G q.2.2 a]| ≤ 2 * C := by
        rw [abs_sub_le_iff]
        have hm := abs_le.mp (abs_integral_le_of_bound_simple μ (fun a : α => G q.2.2 a)
          ((hG.comp (by fun_prop : Measurable fun a : α => (q.2.2, a))).aestronglyMeasurable)
          C (fun a => hGb q.2.2 a))
        have hGq := abs_le.mp (hGb q.2.2 q.1)
        exact ⟨by linarith [hm.1, hGq.2], by linarith [hm.2, hGq.1]⟩
      exact mul_le_mul h1 h2 (abs_nonneg _)
        (by have := hFb q.2.1 q.1; linarith [abs_nonneg (F q.2.1 q.1)])
  unfold covariance
  simp_rw [hFc, hGc, hprod]
  rw [hswap]


end Sandpile
