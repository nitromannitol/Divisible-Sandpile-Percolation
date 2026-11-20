import Sandpile.External.Stopping.WalkIncrementHistory

/-!
# Independence of a clipped walk clock

For a positive time gap, the interpolated walk up to the earlier time and its
clipped stopping clock are independent of future increments. This is the
finite-scale separation used in the weak-filtration argument of Coquet and
Toldo, Section 2.3.1.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Independence of two measurable observations descends through a measurable
map. -/
theorem indepFun_map_of_comp {Ω Ξ E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ξ] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → Ξ) (hg : Measurable g)
    (f : Ξ → E) (h : Ξ → F) (hf : Measurable f) (hh : Measurable h)
    (hind : IndepFun (f ∘ g) (h ∘ g) μ) : IndepFun f h (μ.map g) := by
  let : IsProbabilityMeasure (μ.map g) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have hi := (indepFun_iff_map_prod_eq_prod_map_map
    (hf.comp hg).aemeasurable (hh.comp hg).aemeasurable).1 hind
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hh.aemeasurable).2
  rw [Measure.map_map (hf.prodMk hh) hg, Measure.map_map hf hg, Measure.map_map hh hg]
  exact hi

/-- Once the clipping time precedes a grid time, truncating the integer clock
at that grid time does not change its scaled, clipped value. -/
theorem clipped_scaled_clock_min (c t : ℝ≥0) (hc : 0 < c) (n k : ℕ)
    (ht : c * t ≤ k) :
    min (((min n k : ℕ) : ℝ≥0) / c) t = min ((n : ℝ≥0) / c) t := by
  have hkt : t ≤ (k : ℝ≥0) / c := (le_div_iff₀ hc).2 (by simpa [mul_comm] using ht)
  rw [Nat.cast_min, ← min_div_div_right (show (0 : ℝ≥0) ≤ c from zero_le), min_assoc, min_eq_right hkt]

/-- A stopped walk together with its clipped diffusive stopping clock is
independent of sufficiently later interpolated increments. -/
theorem indepFun_stoppedWalk_clippedClock_future {d : ℕ} [NeZero d]
    (R : ℝ) (hR : 0 < R) (q : Site d) (τ : (ℕ → Site d) → ℕ)
    (hτ : IsWalkStopping τ) (t u : ℝ≥0) (k : ℕ)
    (ht : R ^ 2 * (t : ℝ) ≤ k) (hu : k ≤ ⌊R ^ 2 * (u : ℝ)⌋₊) :
    IndepFun
      (fun X => (LatticeProb.stoppedPath (t : ℝ≥0∞) (diffusiveWalkPath R X),
        min ((τ X : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩) t))
      (fun X => futureIncrementPath u (diffusiveWalkPath R X)) (walkLaw d q) := by
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by change 0 < R ^ 2; positivity
  have ht' : c * t ≤ k := by exact_mod_cast ht
  let f : (ℕ → Site d) → C(ℝ≥0, Continuum.Space d) × ℝ≥0 := fun X =>
    (LatticeProb.stoppedPath (t : ℝ≥0∞) (diffusiveWalkPath R X), min ((τ X : ℝ≥0) / c) t)
  let g : (ℕ → Site d) → C(ℝ≥0, Continuum.Space d) := fun X =>
    futureIncrementPath u (diffusiveWalkPath R X)
  have hτm : Measurable (fun X => min (τ X) k) :=
    LatticeProb.measurable_of_dependsUpTo (fun X Y hXY =>
      IsWalkStopping.min_eq_of_history hτ X Y k hXY)
  have hclock : (fun X => min ((τ X : ℝ≥0) / c) t) =
      (fun X => min (((min (τ X) k : ℕ) : ℝ≥0) / c) t) := by
    funext X
    exact (clipped_scaled_clock_min c t hc (τ X) k ht').symm
  have hfm : Measurable f := by
    dsimp only [f]
    apply Measurable.prodMk
    · exact LatticeProb.continuous_stoppedPath.measurable.comp
        (measurable_const.prodMk (measurable_diffusiveWalkPath R))
    · rw [hclock]
      exact (measurable_of_countable (fun n : ℕ => min ((n : ℝ≥0) / c) t)).comp hτm
  have hgm : Measurable g := (continuous_futureIncrementPath u).measurable.comp
    (measurable_diffusiveWalkPath R)
  have hsrc := indepFun_stoppedWalk_clock_future_driver R q τ hτ t u k ht hu
  let φ : C(ℝ≥0, Continuum.Space d) × ℕ → C(ℝ≥0, Continuum.Space d) × ℝ≥0 :=
    fun p => (p.1, min ((p.2 : ℝ≥0) / c) t)
  have hφ : Measurable φ := measurable_fst.prodMk
    ((measurable_of_countable (fun n : ℕ => min ((n : ℝ≥0) / c) t)).comp measurable_snd)
  have hind := hsrc.comp hφ measurable_id
  have hind' : IndepFun (f ∘ LatticeProb.sitePath q) (g ∘ LatticeProb.sitePath q)
      (LatticeProb.incPathLaw d) := by
    convert hind using 1
    · funext ξ
      simp only [Function.comp_apply, f, φ]
      exact Prod.ext rfl (congrFun hclock _)
    · rfl
  change IndepFun f g ((LatticeProb.incPathLaw d).map (LatticeProb.sitePath q))
  exact indepFun_map_of_comp _ _ (LatticeProb.measurable_sitePath q) f g hfm hgm hind'

end Sandpile.External.Stopping
