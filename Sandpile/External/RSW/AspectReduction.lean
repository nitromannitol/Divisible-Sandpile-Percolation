import Sandpile.External.RSW.AspectDuality
import Sandpile.External.RSW.Homeomorphisms
import Sandpile.External.PlanarRSW

/-!
# Reduction to aspect ratio two

The universal crossing comparison at aspect ratio two implies the comparison at every
positive integer aspect ratio. Dual gluing controls tall rectangles, while primal gluing
controls wide rectangles.
-/

open MeasureTheory Set

noncomputable section

namespace Sandpile.External.RSW

/-- The universal comparison for aspect ratio two. -/
def PlanarRSWAspectTwo : Prop :=
  ∃ ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
    ∀ μ : Measure (Site 2 → ℝ), ∀ [IsProbabilityMeasure μ],
      IsSymmetricPlanarLaw μ → IsAssociatedPlanarLaw μ →
      ∀ n : ℕ, 1 ≤ n → ∀ level : ℝ,
        (ψ (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ) ≤
          μ.real (planarCrossingEvent (4 * n) (2 * n) level)

/-- Taking a root of the complementary probability defines an increasing interval
isomorphism. -/
def complementRootIso (a : ℝ) (ha : 0 < a) : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1 :=
  (unitIntervalReflect.trans (unitIntervalRpow a⁻¹ (inv_pos.mpr ha)).dual).trans
    unitIntervalReflect.symm

/-- The value of the complementary-root isomorphism. -/
theorem complementRootIso_apply (a : ℝ) (ha : 0 < a) (x : Icc (0 : ℝ) 1) :
    (complementRootIso a ha x : ℝ) = 1 - (1 - (x : ℝ)) ^ a⁻¹ := rfl

/-- A bound on powers of complements yields a bound using the complementary-root
isomorphism. -/
theorem complementRootIso_le_of_pow_le (N : ℕ) (hN : 0 < N)
    (x y : Icc (0 : ℝ) 1) (h : (1 - (x : ℝ)) ^ N ≤ 1 - (y : ℝ)) :
    (complementRootIso (N : ℝ) (by exact_mod_cast hN) y : ℝ) ≤ x := by
  have hx : 0 ≤ 1 - (x : ℝ) := sub_nonneg.mpr x.property.2
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr := Real.rpow_le_rpow (pow_nonneg hx N) h (inv_nonneg.mpr hN'.le)
  have he : ((1 - (x : ℝ)) ^ N) ^ (N : ℝ)⁻¹ = 1 - (x : ℝ) := by
    rw [← Real.rpow_natCast, Real.rpow_rpow_inv hx hN'.ne']
  rw [he] at hr
  rw [complementRootIso_apply]
  linarith

/-- The aspect-two comparison implies the universal comparison at every positive integer
aspect ratio. -/
theorem planarRSW_of_aspect_two (h : PlanarRSWAspectTwo) : Sandpile.External.PlanarRSW := by
  obtain ⟨ψ, hψ⟩ := h
  intro ρ hρ
  by_cases hρ1 : ρ = 1
  · subst ρ
    refine ⟨OrderIso.refl _, ?_⟩
    intro μ _ hsym hass n hn level
    simp only [Nat.mul_one, OrderIso.refl_apply]
    rfl
  · have hρ2 : 2 ≤ ρ := by omega
    let N := 4 * ρ + 1
    let M := 2 * ρ + 1
    have hN : 0 < N := by dsimp [N]; omega
    have hM : 0 < M := by dsimp [M]; omega
    let χ := complementRootIso (N : ℝ) (by exact_mod_cast hN)
    let π := unitIntervalRpow (M : ℝ) (by exact_mod_cast hM)
    refine ⟨(χ.trans ψ).trans π, ?_⟩
    intro μ _ hsym hass n hn level
    let a := probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)
    let b := probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (2 * ρ * n) level)
    let c := probabilityInUnitInterval μ (planarCrossingEvent (4 * n) (2 * n) level)
    have hcomp : χ b ≤ a := by
      have hh := fieldCrossing_complement_pow_le μ hsym hass level (by omega : 0 < n) ρ
      exact complementRootIso_le_of_pow_le N hN a b hh
    have hwide : (ψ a : ℝ) ≤ (c : ℝ) := hψ μ hsym hass n hn level
    have hχψ : (ψ (χ b) : ℝ) ≤ (c : ℝ) :=
      (show (ψ (χ b) : ℝ) ≤ (ψ a : ℝ) from ψ.monotone hcomp).trans hwide
    have hp : (ψ (χ b) : ℝ) ^ M ≤ (c : ℝ) ^ M :=
      pow_le_pow_left₀ (ψ (χ b)).property.1 hχψ M
    have hglue := fieldCrossing_two_pow_le μ hsym hass level (by omega : 0 < 2 * n) ρ
    have hlong : planarCrossingEvent ((ρ + 2) * (2 * n)) (2 * n) level ⊆
        planarCrossingEvent (2 * ρ * n) (2 * n) level :=
      planarCrossingEvent_width_height_mono (by nlinarith [hρ2]) (by omega) level
    have hm := measureReal_mono (μ := μ) hlong (measure_ne_top μ _)
    have hewidth : 2 * (2 * n) = 4 * n := by omega
    rw [hewidth] at hglue
    change (c : ℝ) ^ M ≤ _ at hglue
    have hres := hp.trans (hglue.trans hm)
    change ((ψ (χ b) : ℝ) ^ (M : ℝ)) ≤ _
    rw [Real.rpow_natCast]
    exact hres

end Sandpile.External.RSW
