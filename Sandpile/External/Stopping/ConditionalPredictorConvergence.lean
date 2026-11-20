import Sandpile.External.Stopping.FinitePredictorStopping

/-!
# Convergence of conditional predictors

An integrable variable that can be approximated in L¹ by variables measurable
in varying sigma-algebras is approximated in probability by its conditional
expectations in those sigma-algebras.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.External.Stopping

/-- L¹ approximation by measurable variables gives convergence in probability
of the conditional expectations. -/
theorem tendstoInMeasure_condExp_of_l1_approx
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ n, F n ≤ m)
    (f : Ω → ℝ) (hf : Integrable f P) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Integrable (g n) P)
    (hgm : ∀ n, StronglyMeasurable[F n] (g n))
    (hlim : Tendsto (fun n => eLpNorm (f - g n) 1 P) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => P[f | F n]) atTop f := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
  have hbound (n : ℕ) : eLpNorm (P[f | F n] - f) 1 P ≤
      eLpNorm (f - g n) 1 P + eLpNorm (f - g n) 1 P := by
    have hself : P[g n | F n] = g n :=
      condExp_of_stronglyMeasurable (hF n) (hgm n) (hg n)
    have heq : P[f - g n | F n] =ᵐ[P] P[f | F n] - g n := by
      simpa only [hself] using condExp_sub hf (hg n) (F n)
    calc
      eLpNorm (P[f | F n] - f) 1 P ≤
          eLpNorm (P[f | F n] - g n) 1 P + eLpNorm (g n - f) 1 P :=
        by
          have hsplit : P[f | F n] - f = (P[f | F n] - g n) + (g n - f) := by
            funext ω
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
          rw [hsplit]
          exact eLpNorm_add_le (p := 1) le_rfl
      _ = eLpNorm (P[f - g n | F n]) 1 P + eLpNorm (f - g n) 1 P := by
        have hs : eLpNorm (g n - f) 1 P = eLpNorm (f - g n) 1 P := eLpNorm_sub_comm (g n) f 1 P
        rw [eLpNorm_congr_ae heq, hs]
      _ ≤ _ := add_le_add (eLpNorm_condExp_le_eLpNorm (μ := P) (m := F n) (f - g n) le_rfl) le_rfl
  have hz : Tendsto (fun n => eLpNorm (f - g n) 1 P + eLpNorm (f - g n) 1 P)
      atTop (𝓝 0) := by simpa only [add_zero] using hlim.add hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun _ => zero_le) hbound

end Sandpile.External.Stopping
