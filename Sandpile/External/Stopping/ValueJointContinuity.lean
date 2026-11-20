import Sandpile.External.Stopping.ShiftedValueComparison
import Sandpile.External.Stopping.BrownianValueIntrinsic
import Sandpile.Support.D23CubeValueRegularity

/-!
# Joint continuity of Brownian stopping values

Bounded continuous stopping values are jointly continuous in the start and
horizon, for arbitrary Brownian realizations.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Unrestricted Brownian stopping values converge when the starting points
and horizons converge. -/
theorem tendsto_brownianDiscount_of_tendsto_start_horizon
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Continuum.Space d → ℝ≥0 → Ω → Continuum.Space d)
    (hB : ∀ x, Continuum.IsBrownian d x (B x) P)
    (x : Continuum.Space d) (xn : ℕ → Continuum.Space d) (hx : Tendsto xn atTop (𝓝 x))
    (T : ℝ≥0) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Tendsto (fun n => Continuum.brownianDiscount (B (xn n)) P (fun s z => -G s z) (Tn n))
      atTop (𝓝 (Continuum.brownianDiscount (B x) P (fun s z => -G s z) T)) := by
  let D : Continuum.Space d → ℝ≥0 → ℝ := fun u s =>
    Continuum.brownianDiscount (B 0) P (fun t z => -G t (u + z)) s
  have hvalue (u : Continuum.Space d) (s : ℝ≥0) :
      Continuum.brownianDiscount (B u) P (fun t z => -G t z) s = D u s := by
    let C : ℝ≥0 → Ω → Continuum.Space d := fun t ω => u + B 0 t ω
    have hC : Continuum.IsBrownian d u C P := Sandpile.Support.isBrownian_add_const d P (B 0) (hB 0) u
    calc
      _ = Continuum.brownianDiscount C P (fun t z => -G t z) s :=
        brownianDiscount_eq_of_isBrownian P P u (B u) C (hB u) hC s G hGc M hG
      _ = D u s := by
        unfold D Continuum.brownianDiscount
        apply congrArg sSup
        ext a
        simp only [C, Set.mem_setOf_eq, Sandpile.Support.isBrownianStopping_add_const]
  let H : ℝ≥0 := T + 1
  obtain ⟨Δ, hΔi, hΔ, hΔlim⟩ := exists_joint_reward_modulus P 0 (B 0) (hB 0)
    H T Tn hTn x xn hx G hGc M hG
  have hbounded : ∀ᶠ n in atTop, Tn n ≤ H := by
    have ht : T < H := by dsimp [H]; exact lt_add_of_pos_right _ (by norm_num)
    exact (hTn.eventually (Iio_mem_nhds ht)).mono fun _ h => h.le
  have hTH : T ≤ H := by dsimp [H]; exact le_add_of_nonneg_right zero_le
  have hrev (n : ℕ) : ∀ᵐ ω ∂P, ∀ t ≤ H,
      |G ((T : ℝ) - min t T) (x + B 0 (min t T) ω) -
        G ((Tn n : ℝ) - min t (Tn n)) (xn n + B 0 (min t (Tn n)) ω)| ≤ Δ n ω := by
    filter_upwards [hΔ n] with ω hω t ht
    simpa only [abs_sub_comm] using hω t ht
  have hlim : Tendsto (fun n => D (xn n) (Tn n)) atTop (𝓝 (D x T)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hsmall : ∀ᶠ n in atTop, (∫ ω, Δ n ω ∂P) < ε / 2 :=
      hΔlim.eventually (eventually_lt_nhds (half_pos hε))
    filter_upwards [hbounded, hsmall] with n hn hs
    have hu := brownianDiscount_shift_le_add_of_uniform_error P 0 (B 0) (hB 0)
      H (Tn n) T (xn n) x hn G hGc M hG (Δ n) (hΔi n) (hΔ n)
    have hl := brownianDiscount_shift_le_add_of_uniform_error P 0 (B 0) (hB 0)
      H T (Tn n) x (xn n) hTH G hGc M hG (Δ n) (hΔi n) (hrev n)
    change D (xn n) (Tn n) ≤ D x T + ∫ ω, Δ n ω ∂P at hu
    change D x T ≤ D (xn n) (Tn n) + ∫ ω, Δ n ω ∂P at hl
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  simpa only [hvalue] using hlim

end Sandpile.External.Stopping
