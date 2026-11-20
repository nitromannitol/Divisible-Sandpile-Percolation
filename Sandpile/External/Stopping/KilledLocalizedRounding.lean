import Sandpile.External.Stopping.KilledRewardLocalization

/-!
# Rounding localized killed rewards

For bounded continuous rewards, the killed step-walk value and lattice value
are uniformly close at large diffusive scales whenever their possible stopped
positions lie in a common compact set.
-/

open MeasureTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Compact containment of stopped positions lets the temporal rounding error
vanish uniformly over starting sites, box radii and bounded horizons. -/
theorem exists_large_scale_killed_box_grid_comparison {d : ℕ} [NeZero d]
    (K : Set (Continuum.Space d)) (hK : IsCompact K) (T₁ M : ℝ)
    (G : ℝ → Continuum.Space d → ℝ)
    (hG : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ > 0, ∀ R ≥ R₀, ∀ T ∈ Icc (0 : ℝ) T₁, ∀ L : ℝ, ∀ q : Site d,
      0 ≤ ⌊L⌋ →
      (∀ y : Site d, (∀ i, |y i - q i| ≤ ⌊L⌋ + 1) → Lclt.scaledSite R y ∈ K) →
      |sSup (killedStepTimePayoffs R (supBox q L) q T G) -
        killedStoppingSup (supBox q L) ⌊R ^ 2 * T⌋₊ q (fun k X =>
          G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
            (Lclt.scaledSite R (X k)))| ≤ ε := by
  obtain ⟨H, J, hJ, hH, hHK, hHJ, hHM⟩ :=
    exists_compactly_supported_reward_eq_on K hK G hG M hM
  obtain ⟨R₀, hR₀, hmod⟩ :=
    exists_large_scale_uniform_temporal_modulus_of_compact_support J hJ T₁ H hH hHJ
      (half_pos hε)
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR T hT L q hL hcontain
  have hRpos : 0 < R := hR₀.trans_le hR
  have hmodT : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |H s z - H u z| ≤ ε / 2 := by
    intro s hs u hu z hsu
    exact hmod R hR s ⟨hs.1, hs.2.trans hT.2⟩ u ⟨hu.1, hu.2.trans hT.2⟩ z hsu
  have heq : ∀ s y, (∀ i, |y i - q i| ≤ ⌊L⌋ + 1) →
      G s (Lclt.scaledSite R y) = H s (Lclt.scaledSite R y) := by
    intro s y hy
    exact (hHK s _ (hcontain y hy)).symm
  have hs := killedStepTimePayoffs_eq_of_eq_on_box_stopped R L q hL T G H heq
  have hl := killedSet_eq_of_eq_on_box_stopped R L q hL ⌊R ^ 2 * T⌋₊ G H
    ((⌊R ^ 2 * T⌋₊ : ℕ) / R ^ 2) heq
  have hb := abs_sSup_killedStepTimePayoffs_sub_killedGridReward_le hRpos (supBox q L) q
    T M (ε / 2) hT.1 (le_of_lt (half_pos hε)) H hH.measurable hHM hmodT
  rw [hs]
  have hgrid : killedStoppingSup (supBox q L) ⌊R ^ 2 * T⌋₊ q (fun k X =>
      G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2) (Lclt.scaledSite R (X k))) =
      killedStoppingSup (supBox q L) ⌊R ^ 2 * T⌋₊ q (fun k X =>
      H (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2) (Lclt.scaledSite R (X k))) := by
    unfold killedStoppingSup
    convert congrArg sSup hl using 1 <;> congr 2 <;> funext k X <;>
      congr 1 <;> ring
  rw [hgrid]
  linarith

end Sandpile.External.Stopping
