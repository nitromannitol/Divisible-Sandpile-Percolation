import Sandpile.External.Stopping.ConditionalPredictorConvergence

/-!
# Conditional predictors from asymptotic L¹ density

If a target can be approximated arbitrarily well in L¹ by variables measurable
in each sufficiently late sigma-algebra, its conditional expectations converge
in probability to the target.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.External.Stopping

/-- Conditional expectation has at most twice the L¹ error of an integrable
measurable approximant. -/
theorem eLpNorm_condExp_sub_le_two_approx
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : MeasurableSpace Ω) (hF : F ≤ m) (f g : Ω → ℝ)
    (hf : Integrable f P) (hg : Integrable g P) (hgm : StronglyMeasurable[F] g) :
    eLpNorm (P[f | F] - f) 1 P ≤ eLpNorm (f - g) 1 P + eLpNorm (f - g) 1 P := by
  have hself : P[g | F] = g := condExp_of_stronglyMeasurable hF hgm hg
  have heq : P[f - g | F] =ᵐ[P] P[f | F] - g := by
    simpa only [hself] using condExp_sub hf hg F
  calc
    eLpNorm (P[f | F] - f) 1 P ≤ eLpNorm (P[f | F] - g) 1 P + eLpNorm (g - f) 1 P := by
      have hsplit : P[f | F] - f = (P[f | F] - g) + (g - f) := by
        funext ω
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      rw [hsplit]
      exact eLpNorm_add_le (p := 1) le_rfl
    _ = eLpNorm (P[f - g | F]) 1 P + eLpNorm (f - g) 1 P := by
      have hs : eLpNorm (g - f) 1 P = eLpNorm (f - g) 1 P := eLpNorm_sub_comm g f 1 P
      rw [eLpNorm_congr_ae heq, hs]
    _ ≤ _ := add_le_add (eLpNorm_condExp_le_eLpNorm (μ := P) (m := F) (f - g) le_rfl) le_rfl

/-- Conditional predictions converge in probability if arbitrarily accurate
L¹ approximants are eventually available in the corresponding sigma-algebras. -/
theorem tendstoInMeasure_condExp_of_eventual_l1_density
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ n, F n ≤ m)
    (f : Ω → ℝ) (hf : Integrable f P)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : ℕ → Ω → ℝ,
      (∀ n, Integrable (g n) P) ∧ (∀ n, StronglyMeasurable[F n] (g n)) ∧
      ∀ᶠ n in atTop, eLpNorm (f - g n) 1 P ≤ ε) :
    TendstoInMeasure P (fun n => P[f | F n]) atTop f := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨g, hg, hgm, hclose⟩ := happrox (ε / 2) hhalf
  filter_upwards [hclose] with n hn
  have hb := eLpNorm_condExp_sub_le_two_approx P (F n) (hF n) f (g n) hf (hg n) (hgm n)
  calc
    eLpNorm (P[f | F n] - f) 1 P ≤ eLpNorm (f - g n) 1 P + eLpNorm (f - g n) 1 P := hb
    _ ≤ ε / 2 + ε / 2 := add_le_add hn hn
    _ = ε := ENNReal.add_halves ε

end Sandpile.External.Stopping
