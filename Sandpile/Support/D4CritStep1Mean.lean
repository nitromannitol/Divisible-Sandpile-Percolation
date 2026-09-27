/-
Step 1a of the dimension-four percolation proof assembled
(`sandpile.tex:4008-4020`): with the localization radius `A_loc` of
`cor:mean-localization` and the exit horizon `A_ex` chosen once for the whole
law class, the mean of the localized exit value `Y_R` is at least
`2 b₀ log R` with `b₀ = c₀/16`, uniformly in the site and in the law.
-/
import Sandpile.Support.D4CritConstants
import Sandpile.Support.D4CritLocalize
import Sandpile.Support.D4CritStep1
import Sandpile.Support.D4CritExitProb
import Sandpile.Frozen.CriticalTopplingD4
import LatticeProb.Prob.SubGaussian

open LatticeProb

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Sandpile

/-- Step 1a: the mean of the localized exit value is at least `2 b₀ log R`,
uniformly in the site and over the law class. -/
theorem exists_step1_mean (_hVarScale : Sandpile.External.VarianceScale)
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ (c₀ b₀ Aloc : ℝ) (Aex : ℕ), 0 < c₀ ∧ b₀ = c₀ / 16 ∧ 1 ≤ Aloc ∧ 1 ≤ Aex ∧
      ∃ R₀ : ℕ, 2 ≤ R₀ ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ R : ℕ, R₀ ≤ R → ∀ x : Site 4,
          2 * b₀ * Real.log R ≤ ∫ ζ, eaExitValue Aex Aloc R ζ x
            ∂(LatticeProb.iidLaw 4 ν) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, t₁, hCT⟩ :=
    Sandpile.Frozen.critical_toppling_d4 ν₀ θ₀ K₀ hν₀ hθ₀
  obtain ⟨C₁, c₁, hC₁, hc₁, hlocU⟩ :=
    mean_localization_uniform 4 (by norm_num) 1 (by norm_num)
  obtain ⟨Aloc, hAloc1, hAlocSmall⟩ := exists_loc_radius C₀ C₁ c₁ c₀ hC₀ hC₁ hc₁ hc₀
  obtain ⟨Ce, hCe, hexitP⟩ := exists_exit_prob_cube
  obtain ⟨Aex, hAex1, hAexSmall⟩ := exists_exit_horizon Ce hCe
  refine ⟨c₀, c₀ / 16, Aloc, Aex, hc₀, rfl, hAloc1, hAex1, max 2 t₁, le_max_left _ _, ?_⟩
  intro ν hν hmean hvar hexpint hexp R hR x
  haveI := hν
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hRt₁ : t₁ ≤ R ^ 2 := by
    have h1 : t₁ ≤ R := le_trans (le_max_right _ _) hR
    nlinarith
  have hint := integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    hint.abs.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
      exact max_le (le_abs_self z) (abs_nonneg z))
  have hCTν := hCT ν hν hmean hvar hexpint hexp
  have hm := uniform_localized_mean_lower_thresh ν hν hmean hpos c₀ C₀ c₁ C₁ Aloc R t₁
    hRt₁ hc₀ hC₀ hc₁ hC₁ hAloc1 hR2
    (fun t ht => (hCTν.1 t ht).1) (fun t ht => (hCTν.1 t ht).2)
    (hlocU ν hν hpos) hAlocSmall
  have hmea : ∀ w : Site 4, c₀ * Real.log ((R : ℕ) ^ 2) / 2 ≤
      ∫ ζ, localizedOdometer (eaCube w (Aloc * (R : ℝ))) ζ (R ^ 2) w
        ∂(LatticeProb.iidLaw 4 ν) := by
    intro w
    rw [eaCube_eq_supBox]
    exact hm w
  have hm0 : 0 ≤ c₀ * Real.log ((R : ℕ) ^ 2) / 2 := by
    have hlog : 0 ≤ Real.log ((R : ℝ) ^ 2) := by
      refine Real.log_nonneg ?_
      have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR2
      nlinarith
    positivity
  have hp0 : 0 ≤ Ce / (Aex : ℝ) ^ 2 := by positivity
  have hEY := exit_value_mean_lower ν hν hpos Aex Aloc R x
    (c₀ * Real.log ((R : ℕ) ^ 2) / 2) (Ce / (Aex : ℝ) ^ 2) hm0 hp0 hmea
    (hexitP R Aex (by omega) hAex1 x)
  exact exit_value_tail_arith c₀ (c₀ / 16) (Ce / (Aex : ℝ) ^ 2)
    (∫ ζ, eaExitValue Aex Aloc R ζ x ∂(LatticeProb.iidLaw 4 ν)) R hR2 hc₀ rfl
    hAexSmall hEY

end Sandpile
