import Sandpile.External.Stopping.KilledWalkClockCompactness
import Sandpile.External.Stopping.VaryingWeakIntegral
import Sandpile.External.Stopping.VaryingFloorTime

/-!
# Subsequential limits of killed lattice stopping rewards

Along a subsequence, rewards at bounded lattice stopping times converge to a
joint path-clock reward no larger than the limiting cube stopping value.
-/

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped NNReal ENNReal ProbabilityTheory BoundedContinuousFunction

namespace Sandpile.External.Stopping

/-- Killed lattice stopping rewards admit a subsequential limit bounded by
the cube stopping value of the Brownian path limit. -/
theorem exists_killed_walk_stopping_reward_subsequence {d : ℕ} [NeZero d]
    {ι : Type*} [Countable ι]
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (q : ℕ → Site d) (H : ℕ → ℝ≥0) (T c : ℝ≥0) (hc : 0 < c)
    (hH : Tendsto H atTop (𝓝 T)) (hHc : ∀ n, H n ≤ c)
    (τ : ℕ → (ℕ → Site d) → ℕ) (hτ : ∀ n, IsWalkStopping (τ n))
    (hτH : ∀ n X, τ n X ≤ ⌊R n ^ 2 * (H n : ℝ)⌋₊)
    (hkill : ∀ n X j, j < τ n X → X j ∈ supBox (q n) (R n))
    (ν : ProbabilityMeasure C(ℝ≥0, Continuum.Space d))
    (hpath : Tendsto (fun n => diffusiveWalkPathLaw d (R n) (q n)) atTop (𝓝 ν))
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    (hB : Continuum.IsBrownian d a (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
      (ν : Measure C(ℝ≥0, Continuum.Space d)))
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    ∃ (φ : ℕ → ℕ) (L : ℝ), StrictMono φ ∧
      Tendsto (fun n => ∫ X, G
        (((⌊R (φ n) ^ 2 * (H (φ n) : ℝ)⌋₊ : ℕ) - (τ (φ n) X : ℝ)) / R (φ n) ^ 2)
        (Lclt.scaledSite (R (φ n)) (X (τ (φ n) X))) ∂(walkLaw d (q (φ n))))
        atTop (𝓝 L) ∧
      L ≤ Continuum.brownianDiscountCube (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        (ν : Measure C(ℝ≥0, Continuum.Space d)) (fun s z => -G s z) T 1 a := by
  obtain ⟨φ, ρ, hφ, hmarg, hlim, _, hbound⟩ :=
    exists_killed_walk_clock_limit_with_reward_bound R hRpos hR q H T c hc hH hHc τ hτ hτH
      hkill ν hpath a hstart hB time hdense G hGc M hG
  let clock : I → ℝ≥0 := fun u => c * unitClock id u
  have hclock : Continuous clock := continuous_const.mul continuous_unitClock
  let F₀ : C(ℝ × (C(ℝ≥0, Continuum.Space d) × I), ℝ) :=
    ⟨fun p => G (p.1 - (clock p.2.2 : ℝ)) (p.2.1 (clock p.2.2)), by
      exact hGc.comp ((continuous_fst.sub (NNReal.continuous_coe.comp (hclock.comp
          (continuous_snd.comp continuous_snd)))).prodMk
        (continuous_eval.comp ((continuous_fst.comp continuous_snd).prodMk
          (hclock.comp (continuous_snd.comp continuous_snd)))))⟩
  let F : (ℝ × (C(ℝ≥0, Continuum.Space d) × I)) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound F₀ (2 * M) (by
      intro x y
      have hx := hG (x.1 - (clock x.2.2 : ℝ)) (x.2.1 (clock x.2.2))
      have hy := hG (y.1 - (clock y.2.2 : ℝ)) (y.2.1 (clock y.2.2))
      change |F₀ x - F₀ y| ≤ 2 * M
      exact (abs_sub _ _).trans (by dsimp [F₀]; linarith))
  let a (n : ℕ) : ℝ := (⌊R n ^ 2 * (H n : ℝ)⌋₊ : ℝ) / R n ^ 2
  have ha : Tendsto a atTop (𝓝 (T : ℝ)) :=
    tendsto_varying_floor_time_div_sq R (fun n => (H n : ℝ)) hR
      (fun n => (H n).property) (NNReal.continuous_coe.continuousAt.tendsto.comp hH)
  have hrew := tendsto_integral_boundedContinuous_of_parameter _ ρ hlim (a ∘ φ) (T : ℝ)
    (ha.comp hφ.tendsto_atTop) F
  let L : ℝ := ∫ p, G ((T : ℝ) - (clock p.2 : ℝ)) (p.1 (clock p.2)) ∂(ρ : Measure (C(ℝ≥0, Continuum.Space d) × I))
  refine ⟨φ, L, hφ, ?_, ?_⟩
  · have heq (n : ℕ) :
        (∫ p, F (a (φ n), p) ∂(normalizedWalkClockLaw (R (φ n)) (q (φ n)) c
          (τ (φ n)) (LatticeProb.measurable_isWalkStopping (hτ (φ n)) (hτH (φ n))) : Measure _)) =
        ∫ X, G (((⌊R (φ n) ^ 2 * (H (φ n) : ℝ)⌋₊ : ℕ) - (τ (φ n) X : ℝ)) /
          R (φ n) ^ 2) (Lclt.scaledSite (R (φ n)) (X (τ (φ n) X)))
          ∂(walkLaw d (q (φ n))) := by
      change (∫ p, F (a (φ n), p) ∂(walkLaw d (q (φ n))).map
        (fun X => (diffusiveWalkPath (R (φ n)) X,
          normalizedWalkClock (R (φ n)) c (τ (φ n)) X))) = _
      have hm : Measurable (fun X => (diffusiveWalkPath (R (φ n)) X,
          normalizedWalkClock (R (φ n)) c (τ (φ n)) X)) :=
        (measurable_diffusiveWalkPath _).prodMk (measurable_normalizedWalkClock _ _ _
          (LatticeProb.measurable_isWalkStopping (hτ (φ n)) (hτH (φ n))))
      have hFm : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × I => F (a (φ n), p)) :=
        (F.continuous.comp (continuous_const.prodMk continuous_id)).measurable
      rw [integral_map hm.aemeasurable hFm.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards with X
      have hs : diffusiveLatticeClock (R (φ n)) (τ (φ n) X) ≤ c :=
        (diffusiveLatticeClock_le_horizon _ (hRpos (φ n)) _ _ (hτH (φ n) X)).trans (hHc (φ n))
      have hd := decode_normalizedWalkClock (R (φ n)) c hc (τ (φ n)) X hs
      change G (a (φ n) - (c * unitClock id
        (normalizedWalkClock (R (φ n)) c (τ (φ n)) X) : ℝ≥0))
        (diffusiveWalkPath (R (φ n)) X (c * unitClock id
          (normalizedWalkClock (R (φ n)) c (τ (φ n)) X))) = _
      rw [hd, diffusiveWalkPath_diffusiveLatticeClock _ (hRpos (φ n))]
      have htime : ((diffusiveLatticeClock (R (φ n)) (τ (φ n) X) : ℝ≥0) : ℝ) =
          (τ (φ n) X : ℝ) / R (φ n) ^ 2 := rfl
      rw [htime]
      dsimp [a]
      congr 1
      ring
    have htarget : (∫ p, F ((T : ℝ), p) ∂(ρ : Measure (C(ℝ≥0, Continuum.Space d) × I))) = L := rfl
    rw [htarget] at hrew
    simpa only [Function.comp_apply, heq] using hrew
  · have hmarg' : (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst =
        (ν : Measure C(ℝ≥0, Continuum.Space d)) :=
      congrArg (fun p : ProbabilityMeasure C(ℝ≥0, Continuum.Space d) =>
        (p : Measure C(ℝ≥0, Continuum.Space d))) hmarg
    simpa only [L, clock, hmarg'] using hbound

end Sandpile.External.Stopping
