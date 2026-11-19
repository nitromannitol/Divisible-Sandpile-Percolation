import Sandpile.External.RSW.BridgeBound
import Sandpile.External.RSW.InductionClosing

/-!
# Bridge comparisons across scales

A lower bound on a long crossing in terms of a bridge at scale `m` transfers to a
comparison between bridges at scales `m` and `4m`.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A long-crossing comparison yields the corresponding comparison of bridge probabilities
at consecutive geometric scales. -/
theorem kstBridge_four_scale_comparison (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1) (m : ℕ)
    (h : (ψ (probabilityInUnitInterval μ (kstBridgeEvent m)) : ℝ) ≤
      μ.real (bondCrossingEvent (16 * m) (2 * m))) :
    ψ (probabilityInUnitInterval μ (kstBridgeEvent m)) ≤
      probabilityInUnitInterval μ (kstBridgeEvent (4 * m)) := by
  have hsub : bondCrossingEvent (16 * m) (2 * m) ⊆ bondCrossingEvent (4 * (4 * m)) (2 * (4 * m)) :=
    bondCrossingEvent_width_height_mono (by omega) (by omega)
  exact h.trans ((measureReal_mono (μ := μ) hsub (measure_ne_top μ _)).trans
    (measureReal_crossing_le_kstBridge μ ht (4 * m)))

/-- Consecutive comparisons by one interval isomorphism compose into a comparison between
the initial scale and any later scale. -/
theorem exists_intervalIso_comparison_of_steps (f : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (p : ℕ → Icc (0 : ℝ) 1) (h : ∀ k, f (p k) ≤ p (k + 1)) (K : ℕ) :
    ∃ g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1, g (p 0) ≤ p K := by
  induction K with
  | zero => exact ⟨OrderIso.refl _, le_rfl⟩
  | succ K ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨g.trans f, (f.monotone hg).trans (h K)⟩

/-- The square-root closing inequality remains valid when the current bridge probability
vanishes, provided consecutive scales satisfy an interval-isomorphism comparison. -/
theorem sq_le_of_closing_and_scale_steps (f : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (p : ℕ → Icc (0 : ℝ) 1) (h : ∀ k, f (p k) ≤ p (k + 1)) (K : ℕ)
    (hclose : Real.sqrt (p K : ℝ) * (p 0 : ℝ) ≤ p K) :
    (p 0 : ℝ) ^ 2 ≤ p K := by
  obtain ⟨g, hg⟩ := exists_intervalIso_comparison_of_steps f p h K
  exact sq_le_of_sqrt_mul_le_of_scale g (p K) (p 0) hg hclose

end Sandpile.External.RSW
