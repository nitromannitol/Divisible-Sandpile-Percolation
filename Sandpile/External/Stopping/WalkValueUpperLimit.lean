import Sandpile.External.Stopping.WalkStoppingRewardSubsequence

/-!
# Upper limits of lattice stopping values

Near-optimal lattice stopping rules and subsequential compactness bound the
asymptotic lattice value by the stopping value of the limiting path law.
-/

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- Every lattice stopping supremum has a stopping rule within any positive
additive error. -/
theorem exists_walk_stopping_near_value {d : ℕ} (N : ℕ) (q : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ N) ∧
      stoppingSup N q F ≤ (∫ X, F (τ X) X ∂(walkLaw d q)) + ε := by
  let S : Set ℝ := {a | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧
    (∀ X, τ X ≤ N) ∧ a = ∫ X, F (τ X) X ∂(walkLaw d q)}
  have hS : S.Nonempty := by
    refine ⟨_, fun _ => 0, ?_, (fun _ => Nat.zero_le N), rfl⟩
    intro k X Y hXY hk
    exact hk
  have heq : stoppingSup N q F = sSup S := rfl
  have hlt : sSup S - ε < sSup S := sub_lt_self _ hε
  obtain ⟨a, ⟨τ, hτ, hτN, rfl⟩, ha⟩ := exists_lt_of_lt_csSup hS hlt
  exact ⟨τ, hτ, hτN, by rw [heq]; linarith⟩

/-- Lattice grid-horizon stopping values have the stopping value of the weak
path limit as an asymptotic upper bound. -/
theorem eventually_grid_value_le_path_value {d : ℕ} [NeZero d]
    {ι : Type*} [Countable ι]
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (q : ℕ → Site d) (H : ℕ → ℝ≥0) (T : ℝ≥0) (hH : Tendsto H atTop (𝓝 T))
    (ν : ProbabilityMeasure C(ℝ≥0, Continuum.Space d))
    (hpath : Tendsto (fun n => diffusiveWalkPathLaw d (R n) (q n)) atTop (𝓝 ν))
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, stoppingSup ⌊R n ^ 2 * (H n : ℝ)⌋₊ (q n) (fun k X =>
      G (((⌊R n ^ 2 * (H n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
        (Lclt.scaledSite (R n) (X k))) ≤
      Continuum.brownianDiscount (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        (ν : Measure C(ℝ≥0, Continuum.Space d)) (fun s z => -G s z) T + ε := by
  let V : ℝ := Continuum.brownianDiscount
    (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
      (ν : Measure C(ℝ≥0, Continuum.Space d)) (fun s z => -G s z) T
  let F (n : ℕ) (k : ℕ) (X : ℕ → Site d) :=
    G (((⌊R n ^ 2 * (H n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
      (Lclt.scaledSite (R n) (X k))
  by_contra hbad
  have hfreq : ∃ᶠ n in atTop, V + ε < stoppingSup ⌊R n ^ 2 * (H n : ℝ)⌋₊ (q n) (F n) := by
    simpa only [not_le] using (not_eventually.mp hbad)
  obtain ⟨ψ, hψ, hψbad⟩ := extraction_of_frequently_atTop hfreq
  have hnear (n : ℕ) : ∃ τ : (ℕ → Site d) → ℕ,
      IsWalkStopping τ ∧ (∀ X, τ X ≤ ⌊R (ψ n) ^ 2 * (H (ψ n) : ℝ)⌋₊) ∧
      stoppingSup ⌊R (ψ n) ^ 2 * (H (ψ n) : ℝ)⌋₊ (q (ψ n)) (F (ψ n)) ≤
        (∫ X, F (ψ n) (τ X) X ∂(walkLaw d (q (ψ n)))) + ε / 2 :=
    exists_walk_stopping_near_value _ _ _ (ε / 2) (by positivity)
  choose τ hτ hτH hτnear using hnear
  obtain ⟨C, hC⟩ := hH.bddAbove_range
  let c : ℝ≥0 := C + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hHc (n : ℕ) : H (ψ n) ≤ c :=
    (hC ⟨ψ n, rfl⟩).trans (le_add_of_nonneg_right zero_le)
  obtain ⟨φ, L, hφ, hLlim, hLbound⟩ :=
    exists_walk_stopping_reward_subsequence (R ∘ ψ) (fun n => hRpos (ψ n))
      (hR.comp hψ.tendsto_atTop) (q ∘ ψ) (H ∘ ψ) T c hc
      (hH.comp hψ.tendsto_atTop) hHc τ hτ hτH ν
      (hpath.comp hψ.tendsto_atTop) time hdense G hGc M hG
  have hlower : V + ε / 2 ≤ L := by
    apply ge_of_tendsto hLlim
    filter_upwards with n
    have hb := hψbad (φ n)
    have hn := hτnear (φ n)
    change V + ε / 2 ≤ ∫ X, F (ψ (φ n)) (τ (φ n) X) X ∂(walkLaw d (q (ψ (φ n))))
    linarith
  change L ≤ V at hLbound
  linarith

end Sandpile.External.Stopping
