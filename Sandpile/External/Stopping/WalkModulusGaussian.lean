import Sandpile.External.Stopping.ModulusGrid
import Sandpile.External.Stopping.WalkGaussianInterval

/-!
# Gaussian modulus bound for rescaled walks

A deterministic grid cover and the Gaussian maximal-displacement estimate give
an explicit bound on the modulus of the diffusively rescaled walk over a
bounded time window.
-/

open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace Sandpile.External.Stopping

/-- A Gaussian bound on the short-lag modulus over a bounded time interval,
uniformly in the starting site. -/
theorem exists_diffusiveWalk_modulus_gaussian (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (R ε L : ℝ) (δ : ℝ≥0), 0 < R → 0 < δ → 8 ≤ R * ε →
        ∀ x : Site d,
          walkLaw d x {X | ∃ s t : ℝ≥0, (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧
            |(s : ℝ) - t| ≤ δ ∧ ε < dist (diffusiveWalk R s X) (diffusiveWalk R t X)} ≤
            ((⌊L / (δ : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0∞) *
              ENNReal.ofReal (C * Real.exp (-c * ((ε / 4) * R) ^ 2 /
                ((⌊(2 * (δ : ℝ)) * R ^ 2⌋₊ + 1 : ℕ) : ℝ))) := by
  obtain ⟨C, c, hC, hc, hgauss⟩ := exists_diffusiveWalk_interval_gaussian d hd
  refine ⟨C, c, hC, hc, ?_⟩
  intro R ε L δ hR hδ hRε x
  have hsmall : 4 ≤ R * (ε / 2) := by nlinarith
  have hδnonneg : 0 ≤ 2 * (δ : ℝ) := by positivity
  let q : ℝ≥0∞ := ENNReal.ofReal (C * Real.exp (-c * ((ε / 4) * R) ^ 2 /
    ((⌊(2 * (δ : ℝ)) * R ^ 2⌋₊ + 1 : ℕ) : ℝ)))
  have hlocal : ∀ k : ℕ,
      walkLaw d x {X | ∃ u : ℝ≥0, (k : ℝ≥0) * δ ≤ u ∧
        (u : ℝ) ≤ (k : ℝ) * δ + 2 * δ ∧
        ε / 2 < dist (diffusiveWalk R u X) (diffusiveWalk R ((k : ℝ≥0) * δ) X)} ≤ q := by
    intro k
    let t : ℝ≥0 := (k : ℝ≥0) * δ
    have hg := hgauss R (ε / 2) (2 * (δ : ℝ)) hR hδnonneg hsmall t x
      (fun _ => t) (Continuum.isBrownianStopping_const (diffusiveWalk R) t) (fun _ => le_rfl)
    have hsub : {X : ℕ → Site d | ∃ u : ℝ≥0, (k : ℝ≥0) * δ ≤ u ∧
        (u : ℝ) ≤ (k : ℝ) * δ + 2 * δ ∧
        ε / 2 < dist (diffusiveWalk R u X) (diffusiveWalk R ((k : ℝ≥0) * δ) X)} ⊆
      {X : ℕ → Site d | ∃ u : ℝ≥0, t ≤ u ∧ (u : ℝ) ≤ (t : ℝ) + 2 * δ ∧
        ε / 2 ≤ ‖diffusiveWalk R u X - diffusiveWalk R t X‖} := by
      intro X hX
      obtain ⟨u, h₁, h₂, h₃⟩ := hX
      refine ⟨u, h₁, ?_, ?_⟩
      · simpa only [t, NNReal.coe_mul, NNReal.coe_natCast] using h₂
      · simpa only [t, dist_eq_norm] using h₃.le
    have heq : (ε / 2 / 2) * R = (ε / 4) * R := by ring
    exact (measure_mono hsub).trans (by simpa only [q, heq] using hg)
  have hgrid := measure_modulus_le_sum_grid_excursions (walkLaw d x)
    (fun X t => diffusiveWalk R t X) L ε δ hδ
  calc
    _ ≤ ∑ k ∈ Finset.range (⌊L / (δ : ℝ)⌋₊ + 1), q :=
      hgrid.trans (Finset.sum_le_sum fun k _ => hlocal k)
    _ = ((⌊L / (δ : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0∞) * q := by simp [nsmul_eq_mul]

end Sandpile.External.Stopping
