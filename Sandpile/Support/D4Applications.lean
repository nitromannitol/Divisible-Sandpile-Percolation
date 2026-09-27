/-
Applications of critical dimension-four growth to a fixed scenery law.
The eventual comparison extends to every time at least two using concavity.
-/
import Sandpile.Frozen.CriticalTopplingD4
import Sandpile.External.VarianceScaleProved

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

theorem exists_critical_bounds_fixed_four (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ t₀ : ℕ,
      (∀ t : ℕ, t₀ ≤ t → c * Real.log t ≤ meanOdometer (centeredMassLaw 4 ν) t ∧
        meanOdometer (centeredMassLaw 4 ν) t ≤ C * Real.log t) ∧
      (∀ x : Site 4,
        Tendsto (fun t : ℕ => ∫ σ, (odometer σ t x /
          meanOdometer (centeredMassLaw 4 ν) t - 1) ^ 2 ∂centeredMassLaw 4 ν) atTop (𝓝 0) ∧
        ∀ᵐ σ ∂centeredMassLaw 4 ν,
          Tendsto (fun t : ℕ => odometer σ t x / meanOdometer (centeredMassLaw 4 ν) t) atTop (𝓝 1)) := by
  have hv : 0 < (evariance id ν).toReal := ENNReal.toReal_pos hvar.ne' hvar'.ne
  have hs : 0 < Real.sqrt (evariance id ν).toReal := Real.sqrt_pos.mpr hv
  have hvb : ENNReal.ofReal (Real.sqrt (evariance id ν).toReal ^ 2) ≤ evariance id ν := by
    rw [Real.sq_sqrt hv.le, ENNReal.ofReal_toReal hvar'.ne]
  obtain ⟨c, C, hc, hC, t₀, hb⟩ := Frozen.critical_toppling_d4
    (Real.sqrt (evariance id ν).toReal) θ (∫ z, Real.exp (θ * |z|) ∂ν) hs hθ
  have h := hb ν inferInstance hmean hvb hexp le_rfl
  exact ⟨c, C, hc, hC, t₀, h.1, h.2.2⟩

/-- An eventually logarithmic concave mean has logarithmic comparison bounds
at every integer time at least two. -/
theorem logarithmic_bounds_of_eventual (M : ℕ → ℝ) (hzero : M 0 = 0)
    (hmono : Monotone M) (hconc : ∀ n, M (n + 2) - M (n + 1) ≤ M (n + 1) - M n)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) (t₀ : ℕ)
    (hb : ∀ t, t₀ ≤ t → c * Real.log t ≤ M t ∧ M t ≤ C * Real.log t) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ t : ℕ, 2 ≤ t →
      c' * Real.log t ≤ M t ∧ M t ≤ C' * Real.log t := by
  set T := max t₀ 2
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by dsimp [T]; omega : 0 < T)
  have hT2 : 2 ≤ T := le_max_right _ _
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hMT : 0 < M T := (mul_pos hc hlogT).trans_le (hb T (le_max_left _ _)).1
  have hstep := concave_seq_step M hzero hconc
  have hM1 : 0 < M 1 := by
    have h := concave_seq_mul_le M hstep 1 (by omega) T (by omega)
    simp only [Nat.cast_one, mul_one] at h
    nlinarith
  refine ⟨min c (M 1 / Real.log T), max C (M T / Real.log 2),
    lt_min hc (div_pos hM1 hlogT), lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  by_cases hlarge : T ≤ t
  · have hbt := hb t ((le_max_left _ _).trans hlarge)
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hlog.le).trans hbt.1,
      hbt.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog.le)⟩
  · have htT : t ≤ T := (lt_of_not_ge hlarge).le
    have hlogle : Real.log (t : ℝ) ≤ Real.log T := Real.log_le_log ht0 (by exact_mod_cast htT)
    have hlog2 : Real.log (2 : ℝ) ≤ Real.log t := Real.log_le_log (by norm_num) (by exact_mod_cast ht)
    constructor
    · calc min c (M 1 / Real.log T) * Real.log t ≤ (M 1 / Real.log T) * Real.log t :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hlog.le
        _ ≤ (M 1 / Real.log T) * Real.log T := mul_le_mul_of_nonneg_left hlogle (by positivity)
        _ = M 1 := div_mul_cancel₀ _ hlogT.ne'
        _ ≤ M t := hmono (by omega)
    · calc M t ≤ M T := hmono htT
        _ = (M T / Real.log 2) * Real.log 2 := (div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne').symm
        _ ≤ (M T / Real.log 2) * Real.log t := mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ ≤ max C (M T / Real.log 2) * Real.log t :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hlog.le

theorem exists_log_mean_bounds_fixed_four (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      c * Real.log t ≤ meanOdometer (centeredMassLaw 4 ν) t ∧
        meanOdometer (centeredMassLaw 4 ν) t ≤ C * Real.log t := by
  obtain ⟨c, C, hc, hC, t₀, hb, _⟩ := exists_critical_bounds_fixed_four ν hmean hvar hvar' θ hθ hexp
  have hint := integrable_id_of_exp_moment ν θ hθ hexp
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    hint.abs.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
      exact max_le (le_abs_self z) (abs_nonneg z))
  exact logarithmic_bounds_of_eventual _ (meanOdometer_zero 4 ν)
    (meanOdometer_mono (by norm_num) ν hpos)
    (meanOdometer_concave (by norm_num) ν hint hmean hpos) c C hc hC t₀ hb

end Sandpile
