import Sandpile.Continuum.Stopping
import Sandpile.External.Stopping.WalkAldous

/-!
# Rounding stopping times to the walk grid

A stopping time for an interpolated walk can be rounded to a walk stopping time
at the next grid point. The next grid point is used because an interpolated
path on a grid interval can depend on the position at its right endpoint.
This is a preparatory step for the stopping-time estimates in Coquet and Toldo,
*Convergence of values in optimal stopping and convergence of optimal stopping
times*, Section 2.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- A natural-filtration stopping time for a grid-causal process, rounded up
strictly to the next grid point, is a stopping time of the discrete walk. -/
theorem isWalkStopping_floor_add_one_of_grid_causal {d : ℕ}
    (B : ℝ≥0 → (ℕ → Site d) → Continuum.Space d)
    (τ : (ℕ → Site d) → ℝ≥0)
    (hτ : Continuum.IsBrownianStopping B τ)
    (hB : ∀ (k : ℕ) (X Y : ℕ → Site d), (∀ j ≤ k, X j = Y j) →
      ∀ s : ℝ≥0, s ≤ k → B s X = B s Y) :
    IsWalkStopping (fun X => ⌊(τ X : ℝ)⌋₊ + 1) := by
  intro k X Y hXY hk
  have hlt : (τ X : ℝ) < k := by
    have h := Nat.lt_floor_add_one (τ X : ℝ)
    rw [← hk]
    exact_mod_cast h
  have hle : τ X ≤ (k : ℝ≥0) := by exact_mod_cast hlt.le
  have heq : τ Y = τ X :=
    hτ.galmarino (τ X) X Y rfl (fun s hs => hB k X Y hXY s (hs.trans hle))
  simpa only [heq] using hk

/-- The rounded time remains bounded when the original stopping time is bounded. -/
theorem floor_add_one_le_of_le {α : Type*} (τ : α → ℝ≥0) (H : ℝ≥0)
    (hτ : ∀ x, τ x ≤ H) :
    ∀ x, ⌊(τ x : ℝ)⌋₊ + 1 ≤ ⌊(H : ℝ)⌋₊ + 1 := by
  intro x
  exact Nat.add_le_add_right (Nat.floor_mono (by exact_mod_cast hτ x)) 1

/-- A short interval between an interpolated-process stopping time and a later
path-dependent time has a small rounded walk displacement after diffusive
rescaling. Times are measured in units of one walk step. -/
theorem rounded_increment_small (d : ℕ) (hd : 1 ≤ d) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ (H : ℝ≥0) (x : Site d)
        (B : ℝ≥0 → (ℕ → Site d) → Continuum.Space d)
        (τ σ : (ℕ → Site d) → ℝ≥0),
        Continuum.IsBrownianStopping B τ →
        (∀ (k : ℕ) (X Y : ℕ → Site d), (∀ j ≤ k, X j = Y j) →
          ∀ s : ℝ≥0, s ≤ k → B s X = B s Y) →
        (∀ X, τ X ≤ H) →
        (∀ X, τ X ≤ σ X ∧ (σ X : ℝ) ≤ (τ X : ℝ) + δ * R ^ 2) →
        walkLaw d x {X | ε * R ≤
          ((LatticeProb.graphNorm
            (X (⌊(σ X : ℝ)⌋₊ + 1) - X (⌊(τ X : ℝ)⌋₊ + 1)) : ℕ) : ℝ)} ≤
          ENNReal.ofReal η := by
  obtain ⟨δ, R₀, hδ, hR₀, hsmall⟩ := rescaled_increment_small d hd ε η hε hη
  refine ⟨δ, R₀, hδ, hR₀, ?_⟩
  intro R hR H x B τ σ hτ hB hτH hτσ
  let n := ⌊δ * R ^ 2⌋₊ + 1
  have hz : 0 ≤ δ * R ^ 2 := mul_nonneg hδ.le (sq_nonneg R)
  have hn : (n : ℝ) ≤ δ * R ^ 2 + 1 := by
    dsimp [n]
    have hf := Nat.floor_le hz
    push_cast
    linarith
  have hindex : ∀ X, ⌊(τ X : ℝ)⌋₊ + 1 ≤ ⌊(σ X : ℝ)⌋₊ + 1 ∧
      ⌊(σ X : ℝ)⌋₊ + 1 ≤ (⌊(τ X : ℝ)⌋₊ + 1) + n := by
    intro X
    constructor
    · exact Nat.add_le_add_right (Nat.floor_mono (by exact_mod_cast (hτσ X).1)) 1
    · have ht := Nat.lt_floor_add_one (τ X : ℝ)
      have hz' := Nat.lt_floor_add_one (δ * R ^ 2)
      have hs := (hτσ X).2
      have hs' : (σ X : ℝ) <
          ((⌊(τ X : ℝ)⌋₊ + (⌊δ * R ^ 2⌋₊ + 2) : ℕ) : ℝ) := by
        push_cast
        linarith
      have hf := (Nat.floor_lt (show (0 : ℝ) ≤ σ X from (σ X).property)).2 hs'
      dsimp [n]
      omega
  exact hsmall R hR (⌊(H : ℝ)⌋₊ + 1) n (by dsimp [n]; omega) hn x
    (fun X => ⌊(τ X : ℝ)⌋₊ + 1) (fun X => ⌊(σ X : ℝ)⌋₊ + 1)
    (isWalkStopping_floor_add_one_of_grid_causal B τ hτ hB)
    (floor_add_one_le_of_le τ H hτH) hindex

end Sandpile.External.Stopping
