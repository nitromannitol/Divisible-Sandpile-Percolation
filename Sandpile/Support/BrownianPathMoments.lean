import Sandpile.Support.BrownianMaximalMoments
import Sandpile.Continuum.Stopping
import LatticeProb.Analysis.Polynomial.BallVanishing

/-!
# Finite-dimensional Brownian path bounds

A finite-dimensional Brownian path has a measurable bound on a finite horizon
with finite moments of every nonnegative integer order.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

/-- A finite-dimensional Brownian path on a bounded time interval has an
almost-sure measurable bound with all nonnegative integer moments. -/
theorem Sandpile.Support.exists_brownian_path_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x : Sandpile.Continuum.Space d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0) :
    ∃ M : Ω → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ T, ‖B t ω‖ ≤ M ω) ∧
      ∀ n : ℕ, Integrable (fun ω => M ω ^ n) P := by
  classical
  let W : Fin d → ℝ≥0 → Ω → ℝ :=
    fun i t ω => Real.sqrt d * (B t ω i - x i)
  have hWm : ∀ i t, Measurable (W i t) := by
    intro i t
    exact measurable_const.mul (((EuclideanSpace.proj i).continuous.measurable.comp
      (hBm t).measurable).sub measurable_const)
  have hWc : ∀ i ω, Continuous fun t => W i t ω := by
    intro i ω
    exact continuous_const.mul (((EuclideanSpace.proj i).continuous.comp (hBc ω)).sub continuous_const)
  have hex : ∀ i, ∃ M : Ω → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      (∀ ω t, t ≤ T → |W i t ω - W i 0 ω| ≤ M ω) ∧
      ∀ n : ℕ, Integrable (fun ω => M ω ^ n) P := by
    intro i
    exact Sandpile.Support.exists_brownian_increment_bound P (W i) (hB.coord i) (hWm i) (hWc i) T
  choose N hNm hN0 hNbound hNint using hex
  let a : ℝ := (Real.sqrt d)⁻¹
  let M : Ω → ℝ := fun ω => ‖x‖ + a * ∑ i, N i ω
  have ha : 0 ≤ a := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hMm : Measurable M := by
    exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun i _ => hNm i))
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => add_nonneg (norm_nonneg _) (mul_nonneg ha
    (Finset.sum_nonneg fun i _ => hN0 i ω))
  have hbound : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖B t ω‖ ≤ M ω := by
    filter_upwards [hB.start] with ω hstart t ht
    have hcoord : ∀ i : Fin d, |(B t ω - x) i| ≤ a * N i ω := by
      intro i
      have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by
        intro hd0
        exact (Fin.elim0 (hd0 ▸ i))))
      have hsqrt : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
      have hzero : W i 0 ω = 0 := by simp only [W, hstart, sub_self, mul_zero]
      have hh := hNbound i ω t ht
      rw [hzero, sub_zero] at hh
      have he : (B t ω - x) i = a * W i t ω := by
        simp only [W, a, PiLp.sub_apply]
        rw [← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul]
      rw [he, abs_mul, abs_of_nonneg ha]
      exact mul_le_mul_of_nonneg_left hh ha
    have hsum : ‖B t ω - x‖ ≤ a * ∑ i, N i ω := by
      calc
        _ ≤ ∑ i, |(B t ω - x) i| := LatticeProb.norm_le_sum_abs_coordinates _
        _ ≤ ∑ i, a * N i ω := Finset.sum_le_sum fun i _ => hcoord i
        _ = _ := (Finset.mul_sum _ _ _).symm
    calc
      ‖B t ω‖ = ‖(B t ω - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖B t ω - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ M ω := by dsimp [M]; linarith
  refine ⟨M, hMm, hM0, hbound, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simpa only [pow_zero] using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
  · have hLp : ∀ i, MemLp (N i) n P := by
      intro i
      apply (integrable_norm_rpow_iff (hNm i).aestronglyMeasurable
        (by exact_mod_cast hn) (ENNReal.natCast_ne_top n)).mp
      simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
        abs_of_nonneg (hN0 i _)] using hNint i n
    have hsum : MemLp (fun ω => ∑ i, N i ω) n P :=
      memLp_finsetSum Finset.univ (fun i _ => hLp i)
    have hMLp : MemLp M n P := by
      exact (memLp_const ‖x‖).add (hsum.const_mul a)
    have hi := hMLp.integrable_norm_pow hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hM0 _)] using hi
