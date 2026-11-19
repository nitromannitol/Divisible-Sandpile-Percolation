import Sandpile.External.Stopping.WalkScaledBlockCLT
import Sandpile.External.Stopping.FloorTimeLimits

/-!
# Joint limits of walk increments on time intervals

Projected walk increments over finitely many ordered, disjoint positive time
intervals converge jointly to independent Gaussian variables.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.External.Stopping

/-- Disjoint positive time intervals yield independent Gaussian increment limits. -/
theorem tendstoInDistribution_time_interval_blocks
    {ι : Type*} [Fintype ι] (d : ℕ) [NeZero d] (a : ι → Fin d → ℝ)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (s t : ι → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hst : ∀ i, s i < t i)
    (hdisj : ∀ i j, i ≠ j → t i ≤ s j ∨ t j ≤ s i) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) i =>
        (R n)⁻¹ * ∑ k ∈ Finset.range (⌊t i * (R n) ^ 2⌋₊ - ⌊s i * (R n) ^ 2⌋₊),
          LatticeProb.dotSite (a i) (ξ (⌊s i * (R n) ^ 2⌋₊ + k)))
      atTop (fun (z : ι → ℝ) i => z i * Real.sqrt (t i - s i))
      (fun _ => LatticeProb.incPathLaw d)
      (Measure.pi fun i => gaussianReal 0 (Real.toNNReal ((∑ j, (a i j) ^ 2) / d))) := by
  let m : ℕ → ι → ℕ := fun n i => ⌊t i * (R n) ^ 2⌋₊ - ⌊s i * (R n) ^ 2⌋₊
  let v : ℕ → ι → ℕ → ℕ := fun n i k => ⌊s i * (R n) ^ 2⌋₊ + k
  have hm (i : ι) : Tendsto (fun n => m n i) atTop atTop :=
    tendsto_floor_time_block_atTop R hR (s i) (t i) (hs i) (hst i)
  have hv (n : ℕ) (i : ι) : Function.Injective (v n i) := by
    intro x y hxy
    exact Nat.add_left_cancel hxy
  have hpair (n : ℕ) : Pairwise (fun i j => Disjoint
      (Set.range fun k : Fin (m n i) => v n i k)
      (Set.range fun k : Fin (m n j) => v n j k)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨ki, hki⟩ ⟨kj, hkj⟩
    have hik := ki.isLt
    have hjk := kj.isLt
    dsimp [m, v] at hki hkj hik hjk
    rcases hdisj i j hij with h | h
    · have hfloor := Nat.floor_mono (mul_le_mul_of_nonneg_right h (sq_nonneg (R n)))
      omega
    · have hfloor := Nat.floor_mono (mul_le_mul_of_nonneg_right h (sq_nonneg (R n)))
      omega
  have hscale (i : ι) : Tendsto (fun n => Real.sqrt (m n i) / R n) atTop
      (𝓝 (Real.sqrt (t i - s i))) :=
    tendsto_sqrt_floor_time_block_div R hR (s i) (t i) (hs i) (hst i).le
  simpa only [m, v] using tendstoInDistribution_scaled_disjoint_blocks d a m hm v hv hpair R
    (fun i => Real.sqrt (t i - s i)) hscale

end Sandpile.External.Stopping
