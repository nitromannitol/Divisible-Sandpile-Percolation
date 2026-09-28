import Sandpile.Support.MainExplInterpolationLimit
import Sandpile.Support.MainExplBoundedScale

/-!
# The spatial modulus of the interpolated odometer at large scales

The lattice modulus controls the two lower corners, and the cell oscillation controls the
interpolation error at each endpoint.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal
open Sandpile.Continuum

namespace Sandpile

/-- Uniform equicontinuity in probability on compact sets, at sufficiently large scales. -/
theorem exists_interpolation_modulus_eventually
    (hLocalCLT : Sandpile.External.LocalCLT) (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (K : Set (Space d)) (hK : IsCompact K)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      centeredMassLaw d ν {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < δ ∧
        η < |multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z -
          multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z'|}
        ≤ ENNReal.ofReal ε := by
  obtain ⟨ρ, hρ, hKρ⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Space d)
  obtain ⟨a, Ra, ha, hRa, hosc⟩ := exists_odometer_oscillation_at_distance hLocalCLT d hd hd3 ν
    hmean hvar hvar' θ₀ hθ₀ hexp T hT (ρ + 1) (by positivity) (η / 2) (ε / 2)
    (by positivity) (by positivity)
  obtain ⟨Ri, hRi, hi⟩ := exists_interpolation_mesh_gap hLocalCLT d hd hd3 ν
    hmean hvar hvar' θ₀ hθ₀ hexp T hT K hK (η / 4) (ε / 2) (by positivity) (by positivity)
  refine ⟨a / 2, max 1 (max Ra (max Ri (4 * Real.sqrt d / a))), by positivity,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRaR : Ra ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRiR : Ri ≤ R := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hmeshR : 4 * Real.sqrt d / a ≤ R := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hmesh : Real.sqrt d / R ≤ a / 4 := by
    rw [div_le_iff₀ ha] at hmeshR
    rw [div_le_iff₀ hRp]
    nlinarith
  let F : (Site d → ℝ) → Space d → ℝ := fun σ z => multilinearInterp R
    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z
  let L : (Site d → ℝ) → Space d → ℝ := fun σ z =>
    R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ (fun i => ⌊R * z i⌋)
  let Ei : Set (Site d → ℝ) := {σ | ∃ z ∈ K, η / 4 < |F σ z - L σ z|}
  let Eo : Set (Site d → ℝ) := {σ | ∃ y e : Site d, (∀ i, |y i| ≤ ⌈R * (ρ + 1)⌉) ∧
    ‖External.Lclt.scaledSite R e‖ ≤ a ∧
    η / 2 < |R ^ ((d : ℝ) / 2 - 2) * odometerOf (scenery d σ) ⌊T * R ^ 2⌋₊ (y + e) -
      R ^ ((d : ℝ) / 2 - 2) * odometerOf (scenery d σ) ⌊T * R ^ 2⌋₊ y|}
  have hsub : {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < a / 2 ∧ η < |F σ z - F σ z'|}
      ⊆ Ei ∪ Eo := by
    rintro σ ⟨z, hz, z', hz', hdist, hlarge⟩
    by_cases hii : σ ∈ Ei
    · exact Or.inl hii
    by_cases hoo : σ ∈ Eo
    · exact Or.inr hoo
    exfalso
    have he₁ : |F σ z - L σ z| ≤ η / 4 := le_of_not_gt (fun h => hii ⟨z, hz, h⟩)
    have he₂ : |F σ z' - L σ z'| ≤ η / 4 := le_of_not_gt (fun h => hii ⟨z', hz', h⟩)
    let y : Site d := fun i => ⌊R * z i⌋
    let y' : Site d := fun i => ⌊R * z' i⌋
    have hshift : External.Lclt.scaledSite R (y' - y) =
        Support.meshPoint R z' - Support.meshPoint R z := by
      ext i
      simp only [External.Lclt.scaledSite, Support.meshPoint, PiLp.sub_apply,
        PiLp.toLp_apply, Pi.sub_apply, Int.cast_sub]
      ring
    have hedist : ‖External.Lclt.scaledSite R (y' - y)‖ ≤ a := by
      rw [hshift]
      have h₁ := Support.norm_meshPoint_sub_le hRp z
      have h₂ := Support.norm_meshPoint_sub_le hRp z'
      have h₃ := norm_add_le (Support.meshPoint R z' - z') (z' - z)
      have h₄ := norm_add_le
        ((Support.meshPoint R z' - z') + (z' - z)) (z - Support.meshPoint R z)
      have heq : (Support.meshPoint R z' - z') + (z' - z) +
          (z - Support.meshPoint R z) = Support.meshPoint R z' - Support.meshPoint R z := by abel
      rw [heq, norm_sub_rev z] at h₄
      rw [dist_eq_norm, norm_sub_rev] at hdist
      linarith
    have hzn : ‖z‖ ≤ ρ := by
      simpa only [mem_closedBall, dist_zero_right] using hKρ hz
    have hm : |L σ z' - L σ z| ≤ η / 2 := by
      apply le_of_not_gt
      intro hm
      apply hoo
      refine ⟨y, y' - y, (fun i => abs_floor_scaled_coord_le R hR1 ρ z hzn i), hedist, ?_⟩
      have heq : (d : ℝ) / 2 - 2 = -(2 - (d : ℝ) / 2) := by ring
      have hy : y + (y' - y) = y' := by abel
      simpa only [heq, hy, ← odometer_eq_odometerOf] using hm
    have htri₁ := abs_sub_le (F σ z) (L σ z) (L σ z')
    have htri₂ := abs_sub_le (F σ z) (L σ z') (F σ z')
    rw [abs_sub_comm (L σ z) (L σ z')] at htri₁
    rw [abs_sub_comm (L σ z') (F σ z')] at htri₂
    linarith
  calc centeredMassLaw d ν _ ≤ centeredMassLaw d ν (Ei ∪ Eo) := measure_mono hsub
    _ ≤ centeredMassLaw d ν Ei + centeredMassLaw d ν Eo := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hi R hRiR) (hosc R hRaR)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The compact spatial modulus estimate holds uniformly over every scale at least one. -/
theorem exists_interpolation_modulus
    (hLocalCLT : Sandpile.External.LocalCLT) (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (K : Set (Space d)) (hK : IsCompact K)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
      centeredMassLaw d ν {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < δ ∧
        η < |multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z -
          multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z'|}
        ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, R₀, hδ, _, hevent⟩ := exists_interpolation_modulus_eventually hLocalCLT d hd hd3 ν
    hmean hvar hvar' θ₀ hθ₀ hexp T hT K hK ε η hε hη
  obtain ⟨M, C, G, _, hC, hG, hbound⟩ := Support.exists_bounded_scale_interpolation_bound d hd3
    (centeredMassLaw d ν) T (max 1 R₀) hT (le_max_left _ _) K hK ε hε
  refine ⟨min δ (η / (C + 1)), lt_min hδ (div_pos hη (by linarith)), ?_⟩
  intro R hR
  by_cases hlarge : R₀ ≤ R
  · refine (measure_mono ?_).trans (hevent R hlarge)
    rintro σ ⟨z, hz, z', hz', hd, hv⟩
    exact ⟨z, hz, z', hz', hd.trans_le (min_le_left _ _), hv⟩
  · refine (measure_mono ?_).trans hG
    rintro σ ⟨z, hz, z', hz', hd, hv⟩ hσ
    have hRL : R ≤ max 1 R₀ := (le_of_not_ge hlarge).trans (le_max_right _ _)
    have hb := (hbound σ hσ R hR hRL).2 z hz z' hz'
    have hd' : dist z z' < η / (C + 1) := hd.trans_le (min_le_right _ _)
    have hprod : (C + 1) * dist z z' < η := by
      have := (lt_div_iff₀ (show 0 < C + 1 by linarith)).mp hd'
      nlinarith
    have hdist := dist_nonneg (x := z) (y := z')
    linarith

end Sandpile
