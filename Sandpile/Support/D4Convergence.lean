/-
The first-order odometer limit in dimension four. The logarithmic variance
bound gives convergence in L2. Concentration on exponential square-root
scales, followed by monotonicity and mean concavity, gives almost-sure convergence.
-/
import Sandpile.Support.D4Concentration
import Sandpile.Support.D4MeanLower

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

theorem tendsto_ratio_ae_four (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν)
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    {c C c₁ : ℝ} (hc : 0 < c) (hC : 0 < C) (hc₁ : 0 < c₁) {t₀ : ℕ}
    (hconc : ∀ (y : Site 4) (t : ℕ), 2 ≤ t → ∀ (s : ℝ), 0 ≤ s →
      centeredMassLaw 4 ν
          {σ | s ≤ |odometer σ t y - meanOdometer (centeredMassLaw 4 ν) t|} ≤
        ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2 / Real.log t) s))))
    (hlower : ∀ t : ℕ, t₀ ≤ t →
      c₁ * Real.log t ≤ meanOdometer (centeredMassLaw 4 ν) t)
    (x : Site 4) :
    ∀ᵐ σ ∂(centeredMassLaw 4 ν),
      Tendsto (fun t : ℕ => odometer σ t x /
        meanOdometer (centeredMassLaw 4 ν) t) atTop (𝓝 1) := by
  classical
  set P : Measure (Site 4 → ℝ) := centeredMassLaw 4 ν with hP
  set M : ℕ → ℝ := fun t => meanOdometer P t with hMdef
  set T₀ := max t₀ 2
  set n : ℕ → ℕ := scaleTime T₀ with hn
  have hd : 1 ≤ (4 : ℕ) := by norm_num
  have hn2 (k : ℕ) : 2 ≤ n k := (le_max_right _ _).trans (le_scaleTime T₀ k)
  have hlog (k : ℕ) : 0 < Real.log (n k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by have := hn2 k; omega : 1 < n k))
  have hlow (k : ℕ) : c₁ * Real.log (n k) ≤ M (n k) :=
    hlower (n k) ((le_max_left _ _).trans (le_scaleTime T₀ k))
  have hMscale (k : ℕ) : c₁ * Real.sqrt (k : ℝ) ≤ M (n k) :=
    (mul_le_mul_of_nonneg_left (sqrt_le_log_scaleTime T₀ k) hc₁.le).trans (hlow k)
  have hM0 : M 0 = 0 := meanOdometer_zero 4 ν
  have hMnn : ∀ t : ℕ, 0 ≤ M t := by
    intro t
    have h : M 0 ≤ M t := meanOdometer_mono hd ν hpos (Nat.zero_le t)
    rw [hM0] at h
    exact h
  have hMpos : ∀ k : ℕ, 1 ≤ k → 0 < M (n k) := by
    intro k hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have : (0 : ℝ) < c₁ * Real.sqrt (k : ℝ) := by positivity
    exact lt_of_lt_of_le this (hMscale k)
  -- Borel-Cantelli at the level `ε = 1/(j+1)`
  have hBC : ∀ j : ℕ, ∀ᵐ σ ∂P, ∀ᶠ k in atTop,
      |odometer σ (n k) x - M (n k)| < (1 / ((j : ℝ) + 1)) * M (n k) := by
    intro j
    set ε : ℝ := 1 / ((j : ℝ) + 1) with hε
    have hεpos : 0 < ε := by positivity
    set β : ℝ := c * min ((ε * c₁) ^ 2) (ε * c₁) with hβ
    have hβpos : 0 < β := by positivity
    set g : ℕ → ℝ := fun k => C * Real.exp (-(β * (k : ℝ) ^ ((1 : ℝ) / 2)))
      with hg
    have hgnn : ∀ k, 0 ≤ g k := fun k => by positivity
    have hgsum : Summable g := (summable_exp_neg_rpow hβpos (by norm_num : (0 : ℝ) < 1 / 2)).mul_left _
    have hbound : ∀ k : ℕ,
        P {σ | ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|} ≤ ENNReal.ofReal (g k) := by
      intro k
      have hsnn : 0 ≤ ε * M (n k) := mul_nonneg hεpos.le (hMnn _)
      refine le_trans (hconc x (n k) (hn2 k) (ε * M (n k)) hsnn) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      set s : ℝ := ε * M (n k)
      set L : ℝ := Real.log (n k : ℝ)
      have hL : 0 < L := hlog k
      have hsl : ε * c₁ * L ≤ s := by
        have := mul_le_mul_of_nonneg_left (hlow k) hεpos.le
        dsimp [s, L]
        nlinarith
      have hsql : (ε * c₁) ^ 2 * L ≤ s ^ 2 / L := by
        rw [le_div_iff₀ hL]
        have := pow_le_pow_left₀ (show 0 ≤ ε * c₁ * L by positivity) hsl 2
        nlinarith
      have hmin : min ((ε * c₁) ^ 2) (ε * c₁) * L ≤ min (s ^ 2 / L) s := by
        rw [min_mul_of_nonneg _ _ hL.le]
        exact min_le_min hsql hsl
      have hroot : β * Real.sqrt (k : ℝ) ≤ c * min (s ^ 2 / L) s := by
        have h1 := mul_le_mul_of_nonneg_left (sqrt_le_log_scaleTime T₀ k) hβpos.le
        have h2 := mul_le_mul_of_nonneg_left hmin hc.le
        dsimp [β, L] at *
        nlinarith
      have hexp : Real.exp (-(c * min (s ^ 2 / L) s)) ≤
          Real.exp (-(β * (k : ℝ) ^ ((1 : ℝ) / 2))) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.exp_le_exp.mpr (by linarith)
      exact mul_le_mul_of_nonneg_left hexp hC.le
    have hsum : ∑' k : ℕ, P {σ | ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|} ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
      rw [← ENNReal.ofReal_tsum_of_nonneg hgnn hgsum]
      exact ENNReal.ofReal_ne_top
    have h0 := MeasureTheory.measure_setOf_frequently_eq_zero (μ := P)
      (p := fun k σ => ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|) hsum
    have hae : ∀ᵐ σ ∂P, ∀ᶠ k in atTop,
        ¬ (ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|) := by
      have h1 : {σ : Site 4 → ℝ |
            ¬ (∀ᶠ k in atTop, ¬ (ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|))}
          = {σ : Site 4 → ℝ |
            ∃ᶠ k in atTop, ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|} := by
        ext σ
        simp only [Set.mem_setOf_eq, Filter.not_eventually, not_not]
      rw [ae_iff, h1]
      exact h0
    filter_upwards [hae] with σ hσ
    filter_upwards [hσ] with k hk
    exact lt_of_not_ge hk
  have hall : ∀ᵐ σ ∂P, ∀ j : ℕ, ∀ᶠ k in atTop,
      |odometer σ (n k) x - M (n k)| < (1 / ((j : ℝ) + 1)) * M (n k) :=
    MeasureTheory.ae_all_iff.2 hBC
  filter_upwards [hall] with σ hσ
  have humono : Monotone fun t : ℕ => odometer σ t x := by
    intro s t hst
    have h1 : odometer σ s x = odometerOf (scenery 4 σ) s x :=
      congrFun (odometer_eq_odometerOf σ s) x
    have h2 : odometer σ t x = odometerOf (scenery 4 σ) t x :=
      congrFun (odometer_eq_odometerOf σ t) x
    simp only [h1, h2]
    exact odometerOf_mono_time (scenery 4 σ) x hst
  refine tendsto_ratio_of_scales (u := fun t : ℕ => odometer σ t x) (m := M) (n := n)
    humono (meanOdometer_mono hd ν hpos) (tendsto_scaleTime T₀) ?_
  intro δ hδ
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  have hjnn : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have hev : ∀ᶠ k : ℕ in atTop,
      (|odometer σ (n k) x - M (n k)| < (1 / ((j : ℝ) + 1)) * M (n k) ∧
        M (n (k + 1)) ≤ (1 + δ) * M (n k)) ∧ 1 ≤ k :=
    ((hσ j).and (meanOdometer_scale_ratio hd ν hint hmean hpos T₀ hδ)).and
      (eventually_ge_atTop 1)
  obtain ⟨K, hK⟩ := hev.exists_forall_of_atTop
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨⟨habs, hrat⟩, hk1⟩ := hK k hk
  have hmp : 0 < M (n k) := hMpos k hk1
  have hδabs : |odometer σ (n k) x - M (n k)| < δ * M (n k) := by
    refine lt_of_lt_of_le habs ?_
    exact mul_le_mul_of_nonneg_right hj.le (hMnn _)
  rw [abs_lt] at hδabs
  exact ⟨hmp, by linarith [hδabs.1], by linarith [hδabs.2], hrat⟩

/-- The logarithmic mean dominates the square root of the variance. -/
theorem tendsto_ratio_L2_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : Integrable (fun z => z ^ 2) ν)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {t₀ : ℕ}
    (hlower : ∀ t : ℕ, t₀ ≤ t → c₁ * Real.log t ≤ meanOdometer (centeredMassLaw 4 ν) t)
    (x : Site 4) :
    Tendsto (fun t : ℕ => ∫ σ, (odometer σ t x /
      meanOdometer (centeredMassLaw 4 ν) t - 1) ^ 2 ∂(centeredMassLaw 4 ν)) atTop (𝓝 0) := by
  obtain ⟨V, hV, hb⟩ := exists_odometer_variance_bound_four hVS ν hsq
  set m : ℕ → ℝ := fun t => meanOdometer (centeredMassLaw 4 ν) t
  have hnonneg : ∀ t : ℕ, 0 ≤ ∫ σ, (odometer σ t x / m t - 1) ^ 2 ∂(centeredMassLaw 4 ν) :=
    fun t => integral_nonneg fun σ => sq_nonneg _
  have hlog : Tendsto (fun t : ℕ => Real.log (t : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (g := fun t : ℕ => (2 * V / c₁ ^ 2) / Real.log t)
    (Eventually.of_forall hnonneg) ?_ ((tendsto_const_nhds (x := 2 * V / c₁ ^ 2)).div_atTop hlog)
  filter_upwards [eventually_ge_atTop (max t₀ 2)] with t ht
  have ht0 : t₀ ≤ t := (le_max_left _ _).trans ht
  have ht2 : 2 ≤ t := (le_max_right _ _).trans ht
  have hL : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hl : c₁ * Real.log t ≤ m t := hlower t ht0
  have hm : 0 < m t := (mul_pos hc₁ hL).trans_le hl
  have hEq : ∫ σ, (odometer σ t x / m t - 1) ^ 2 ∂(centeredMassLaw 4 ν)
      = (∫ σ, (odometer σ t x - m t) ^ 2 ∂(centeredMassLaw 4 ν)) / m t ^ 2 := by
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
    field_simp
  rw [hEq]
  have hnum : (∫ σ, (odometer σ t x - m t) ^ 2 ∂(centeredMassLaw 4 ν))
      ≤ 2 * V * Real.log t := by
    have h1 := hb t x
    have h2 := mul_le_mul_of_nonneg_left (log_add_two_le_two_log t ht2) hV
    nlinarith
  have hden : c₁ ^ 2 * Real.log (t : ℝ) ^ 2 ≤ m t ^ 2 := by
    have := pow_le_pow_left₀ (mul_pos hc₁ hL).le hl 2
    nlinarith
  calc (∫ σ, (odometer σ t x - m t) ^ 2 ∂(centeredMassLaw 4 ν)) / m t ^ 2
      ≤ (2 * V * Real.log t) / m t ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ (2 * V * Real.log t) / (c₁ ^ 2 * Real.log (t : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (2 * V / c₁ ^ 2) / Real.log t := by field_simp

end Sandpile
