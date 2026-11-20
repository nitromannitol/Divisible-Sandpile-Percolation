import Sandpile.External.Stopping.CompactRewardModulus
import Mathlib.Topology.UrysohnsLemma

/-!
# Compactly supported reward cutoffs

A bounded continuous reward can be replaced by a continuous reward with common
compact spatial support, without changing it on a prescribed compact set or
increasing its bound.
-/

open Set

namespace Sandpile.External.Stopping

/-- A bounded continuous reward admits a compactly supported spatial cutoff
which agrees with it on any given compact set and preserves its bound. -/
theorem exists_compactly_supported_reward_eq_on
    {E : Type*} [MetricSpace E] [LocallyCompactSpace E] (K : Set E) (hK : IsCompact K)
    (G : ℝ → E → ℝ) (hG : Continuous (fun p : ℝ × E => G p.1 p.2))
    (M : ℝ) (hM : ∀ s z, |G s z| ≤ M) :
    ∃ (H : ℝ → E → ℝ) (L : Set E), IsCompact L ∧
      Continuous (fun p : ℝ × E => H p.1 p.2) ∧
      (∀ s z, z ∈ K → H s z = G s z) ∧
      (∀ s z, z ∉ L → H s z = 0) ∧
      (∀ s z, |H s z| ≤ M) := by
  obtain ⟨f, hfK, _, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  refine ⟨fun s z => f z * G s z, tsupport f, hfc, ?_, ?_, ?_, ?_⟩
  · exact (f.continuous.comp continuous_snd).mul hG
  · intro s z hz
    have hf : f z = 1 := hfK hz
    simp [hf]
  · intro s z hz
    have hf : f z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [hf]
  · intro s z
    have h0 : 0 ≤ f z := (hf01 z).1
    have h1 : f z ≤ 1 := (hf01 z).2
    have habs : |f z| ≤ 1 := by simpa [abs_of_nonneg h0] using h1
    rw [abs_mul]
    have := hM s z
    have hprod : |f z| * |G s z| ≤ 1 * M :=
      mul_le_mul habs this (abs_nonneg _) (by positivity)
    simpa using hprod

end Sandpile.External.Stopping
